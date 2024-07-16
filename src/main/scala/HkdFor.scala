package com.tschuchort.hkd

import scala.compiletime.*
import scala.deriving.Mirror
import scala.util.chaining.*
import scala.quoted.*
import scala.quoted.runtime.StopMacroExpansion
import scala.collection.MapView.Id
import scala.annotation.tailrec
import shapeless3.deriving.K11
import shapeless3.deriving.K0
import scala.reflect.ClassTag
import scala.reflect.TypeTest
import scala.annotation.targetName
import izumi.reflect.Tag
import shapeless3.deriving.internals.ErasedInstances
import scala.util.NotGiven
import scala.util.boundary
import scala.annotation.experimental
import scala.annotation.static
import scala.runtime.Tuples
import scala.runtime.TupleXXL
import internal.{*, given}

type HkdFor_[T] = [F[_]] =>> HkdFor[T, F]

object HkdFor_ :
  def apply[T] = new PartialApplHelper[T]

  class PartialApplHelper[T] extends Dynamic:
    // noinspection TypeAnnotation
    inline def applyDynamic[F[_]](methodName: "apply")(inline args: Any*) =
      HkdFor.applyDynamic[T, F](methodName)(args*)

    // noinspection TypeAnnotation
    inline def applyDynamicNamed[F[_]](methodName: "apply")(inline args: (String, Any)*) =
      HkdFor.applyDynamicNamed[T, F](methodName)(args*)

    def unapply[F[_]](h: HkdFor_[T][F])(using m: Mirror.ProductOf[T]): Tuple.Map[m.MirroredElemTypes, F] =
      HkdFor.unapply[T, F](h)

    /** When an unapply method like this is called and `F` is not explicitly given, then `F` can not be inferred correctly:
      * {{{
      *    HkdFor_[Foo][Option](???) match
      *      case HkdFor_[Foo](a, b, c) => ??? // F is inferred as some unknown F$1 instead of Option
      * }}}
      * Because a type test introduces a level of indirection and the inference algorithm cannot "carry" the F through multiple
      * levels of indirection. We need to apply the type test ourselves, so that we remain in control of type inference.
      */
    transparent inline def unapply[S, F[_]](using inline m: Mirror.ProductOf[T])(using
        tt: TypeTest[com.tschuchort.hkd.HkdFor$package.HkdFor[S, F], com.tschuchort.hkd.HkdFor$package.HkdFor[T, F]])(
        h: com.tschuchort.hkd.HkdFor$package.HkdFor[S, F]
    ): Option[Any] | Boolean = ${ unapplyWithTypeTestImpl[T, S, F]('h, 'tt, 'm) }

  private def unapplyWithTypeTestImpl[T: Type, S: Type, F[_]: Type](using q: Quotes)(
      h: Expr[com.tschuchort.hkd.HkdFor$package.HkdFor[S, F]],
      tt: Expr[TypeTest[com.tschuchort.hkd.HkdFor$package.HkdFor[S, F], com.tschuchort.hkd.HkdFor$package.HkdFor[T, F]]],
      m: Expr[Mirror.ProductOf[T]]
  ): Expr[Option[Any]] | Expr[Boolean] =
    import q.reflect.{*, given}

    val fieldTypes = m match
      case '{
            type elems <: Tuple;
            $m: Mirror.Product { type MirroredElemTypes = `elems` }
          } =>
        tupleToTypes[elems].map { case '[field] => TypeRepr.of[F[field]] }

    fieldTypes.length match
      case 0 => '{ ${ tt }.unapply($h).isDefined }
      case l if l <= Tuples.MaxSpecialized =>
        type TupleL <: Tuple
        given Type[TupleL] = Symbol.classSymbol("scala.Tuple" + l).typeRef
          .appliedTo(fieldTypes.toList).asType.asInstanceOf

        '{
          ${ tt }.unapply($h).map { (x: com.tschuchort.hkd.HkdFor$package.HkdFor[T, F]) =>
            Tuples.fromProduct(x).asInstanceOf[TupleL]
          }: Option[TupleL]
        }

      case _ => report.errorAndAbort(s"Only types with 0 to ${Tuples.MaxSpecialized} fields are supported by this extractor", h)

opaque type HkdFor[T, F[_]] <: Dynamic & Product = HkdForImpl[T]
// ^ opaque type can not have `Product & Selectable` bounds or the warning for "type test can not be checked at runtime" will not
// appear for some reason, despite the fact that those interfaces are not `Matchable`. Subtype relations should instead be supplied
// by given <:< instances or implicit conversions.

extension [T, F[_]](self: HkdFor[T, F]) {
  // noinspection TypeAnnotation
  inline def applyDynamic(methodName: String)(inline args: Any*) =
    ${ copyDynamicNamedImpl[T, F]('self, 'methodName, 'args) }

  // noinspection TypeAnnotation
  inline def applyDynamicNamed(methodName: String)(inline args: (String, Any)*) =
    ${ copyDynamicNamedImpl[T, F]('self, 'methodName, 'args) }
}

private def copyDynamicNamedImpl[T: Type, F[_]: Type](
    thisExpr: Expr[HkdFor[T, F]],
    methodNameExpr: Expr[String],
    argsExpr: Expr[Seq[Any | (String, Any)]]
)(using q: Quotes) =
  import q.reflect.{*, given}
  requireDynamicMethodName(expectedName = "copy", name = methodNameExpr, methodOwnerType = TypeRepr.of[HkdFor[T, F]])

  val paramNamesTypesValues: Seq[(Option[String], TypeRepr, Expr[Any])] = parseDynamicArgsExpr(argsExpr)

  val tMirror = Expr.summonOrAbort[Mirror.ProductOf[T]]

  val normalizedParams = checkAndNormalizeParams(
    expectedParamNamesTypesDefaults =
      TypeRepr.of[T].caseFieldsWithTypes.map { case (name, typeRep) =>
        val default = '{ $thisExpr.selectDynamic(${ Expr(name) })(using $tMirror) }

        typeRep.asType match
          case '[fieldType] => (name, TypeRepr.of[F[fieldType]], Some(default))
      },
    paramNamesTypesValues
  )

  val ctorArgs = Expr.ofSeq(normalizedParams.map { case (name, _, expr) => Expr.ofTuple((Expr(name), expr)) })

  val (tClass, tName, fName) =
    Expr.summonAllOrAbort[(HkdFor.TypeTag[T], TypeName[T], TypeName[F])]

  '{
    new HkdForImpl[T](${ ctorArgs }*)(using $tMirror, $tName, $tClass)
      .asInstanceOf[com.tschuchort.hkd.HkdFor$package.HkdFor[T, F]]
  }

object HkdFor extends Dynamic:

  /*given typeTestStaticUpcast[T, S <: T, F[_], G[_]](using ImplicitsPriority.L4)(using
      HkdFor[S, F] <:< HkdFor[T, G]
  ): TypeTest[HkdFor[S, F], HkdFor[T, G]] with {
    override def unapply(x: HkdFor[S, F]): Some[x.type & HkdFor[T, G]] =
      println("typeTestStaticUpcast")
      Some(x.asInstanceOf[x.type & HkdFor[T, G]])
  }*/

  given typeTestDowncastDynamicTComplexF[T, S <: T, F[_], G[_]](using ImplicitsPriority.L3)(using sClass: TypeTag[S])(using
      com.tschuchort.hkd.HkdFor$package.HkdFor[S, G] <:< com.tschuchort.hkd.HkdFor$package.HkdFor[S, F]
  ): TypeTest[HkdFor[T, G], HkdFor[S, F]] with {
    override def unapply(x: HkdFor[T, G]): Option[x.type & HkdFor[S, G]] =
      x match // in this scope we know that HkdFor =:= (HkdForImpl <: Matchable)
        case _x: (x.type & HkdForImpl[?]) if (_x.tClass <:< sClass) =>
          Some(_x.asInstanceOf[x.type & HkdFor[S, F]])
        case _ => None
  }

  given typeTestDowncastDynamicTSimpleF[T, S <: T, F[_], G <: [A] =>> F[A]](using ImplicitsPriority.L4)(using
      sClass: TypeTag[S]
  ): TypeTest[com.tschuchort.hkd.HkdFor$package.HkdFor[T, G], com.tschuchort.hkd.HkdFor$package.HkdFor[S, F]]
  with {
    override def unapply(x: com.tschuchort.hkd.HkdFor$package.HkdFor[T, G])
        : Option[x.type & com.tschuchort.hkd.HkdFor$package.HkdFor[S, F]] =
      x match // in this scope we know that HkdFor =:= (HkdForImpl <: Matchable)
        case _x: (x.type & HkdForImpl[?]) if (_x.tClass <:< sClass) =>
          Some(_x.asInstanceOf[x.type & com.tschuchort.hkd.HkdFor$package.HkdFor[S, F]])
        case _ => None
  }

  given typeTestHkdForErasedF[T](using ImplicitsPriority.L2)(using
      tClass: TypeTag[T]
  ): TypeTest[HkdFor[Any, [_] =>> Any], HkdFor[T, [_] =>> Any]] with {
    override def unapply(x: HkdFor[Any, [_] =>> Any]): Option[x.type & HkdFor[T, [_] =>> Any]] =
      x match // in this scope we know that HkdFor =:= (HkdForImpl <: Matchable)
        case _x: (x.type & HkdForImpl[?]) if (_x.tClass <:< tClass) =>
          Some(_x.asInstanceOf[x.type & HkdFor[T, [_] =>> Any]])
        case _ => None
  }

  given typeTestHkdForErasedTErasedF(using ImplicitsPriority.L1): TypeTest[Matchable, HkdFor[Any, [_] =>> Any]] with {
    override def unapply(x: Matchable): Option[x.type & HkdFor[Any, [_] =>> Any]] =
      x match
        case _x: (x.type & HkdForImpl[?]) =>
          Some(_x.asInstanceOf[x.type & HkdFor[Any, [_] =>> Any]])
        case _ => None
  }

  inline given typeTestFallbackUnrelatedClasses[T, S, F[_], G[_]](using ImplicitsPriority.L1)(
      using
      NotGiven[T <:< S],
      NotGiven[S <:< T])
      : TypeTest[com.tschuchort.hkd.HkdFor$package.HkdFor[S, F], com.tschuchort.hkd.HkdFor$package.HkdFor[T, G]] =
    error(
      "this case is unreachable since " + showType[com.tschuchort.hkd.HkdFor$package.HkdFor[S, F]] + " and " + showType[
        com.tschuchort.hkd.HkdFor$package.HkdFor[T, G]] +
        " are unrelated. " + showType[T] + " is not a subtype of " + showType[S]
    )

  given unionOfSubtypesEqualsParent[T, F[_]](using ImplicitsPriority.L3)(
      using m: Mirror.SumOf[HkdFor[T, F]]): (HkdFor[T, F] =:= Tuple.Union[m.MirroredElemTypes]) =
    scala.<:<.refl.asInstanceOf

  /** Subtype relationship where the type functions are simple subtypes of each other, for example forall `A`. `Some[A] <:
    * Option[A]` by definition.
    */
  given subtypeWithObviousF[T, S <: T, G[_], F <: [A] =>> G[A]](using ImplicitsPriority.L2): (HkdFor[S, F] <:< HkdFor[T, G]) =
    scala.<:<.refl.asInstanceOf

  /** Subtype relationship where the type functions are not related to each other by definition, for example two match type
    * families that happen to have the same result for all fields in [[S]], despite being different:
    * {{{
    *       type F1[X] = X match
    *         String => String
    *         Int => Int
    *         Boolean => Any
    *
    *       type F2[X] = X match
    *         String => String
    *         Int => Int
    *         Boolean => Nothing
    *
    *       case class Foo(a: Int, b: String)
    * }}}
    * forall `A` in `Mirror.ProductOf[Foo].MirroredElemTypes = (Int, String)`. `F1[A] <: F2[A]` but not `F1[Boolean] <:
    * F2[Boolean]`.
    */
  inline given subtypeWithComplexF[T, S <: T, F[_], G[_]](using ImplicitsPriority.L1): (HkdFor[S, F] <:< HkdFor[T, G]) =
    // It seems that implicit parameters in general just mess up the type inference for the type parameters
    // of <:< givens. Thus, the summoning of all needed implicits has to be deferred to the function body with
    // `summonInline` or `Expr.summon` so that so that type parameters are inferred independently. If no given
    // instance is found, there will be a compile-error and the compiler will automatically skip this given definition.
    ${ subtypeWithComplexFImpl[T, S, F, G] }

  private def subtypeWithComplexFImpl[T: Type, S <: T: Type, F[_]: Type, G[_]: Type](using
      q: Quotes
  ): Expr[HkdFor[S, F] <:< HkdFor[T, G]] =
    import q.reflect.{*, given}

    val allLeafs: Seq[Type[?]] = Expr.summonOrAbort[AdtHierarchyLeafs[S]] match
      case '{
            type leafTypes <: Tuple;
            $al: AdtHierarchyLeafs[S] { type MirroredLeafTypes = `leafTypes` }
          } =>
        tupleToTypes[leafTypes]

    allLeafs.foreach { case '[leafType] =>
      Expr.summonOrAbort[Mirror.ProductOf[leafType]] match
        case '{
              type elems <: Tuple;
              $m: Mirror.ProductOf[s] { type MirroredElemTypes = `elems` }
            } =>
          tupleToTypes[elems].foreach { case '[field] =>
            Implicits.search(TypeRepr.of[F[field] <:< G[field]]) match
              case iss: ImplicitSearchSuccess => ()
              case isf: ImplicitSearchFailure =>
                report.errorAndAbort(
                  s"Could not prove that HkdFor[${Type.show[S]}, ${Type.show[F]}]" +
                    s" <: HkdFor[${Type.show[T]}, ${Type.show[G]}] because ${Type.show[leafType]}, " +
                    s"a possible subtype of ${Type.show[S]}, has a field of type ${Type.show[field]}." +
                    "\n" + "-".repeat(30) + "\n" +
                    isf.explanation +
                    "\n" + "-".repeat(30) + "\n" +
                    s"Hint: You may want to match HkdFor[${Type.show[S]}, ${Type.show[[_] =>> Any]}] and/or cast instead."
                )
          }
    }

    '{ scala.<:<.refl.asInstanceOf[HkdFor[S, F] <:< HkdFor[T, G]] }

  extension [T, F[_]](self: HkdFor[T, F])
    @experimental
    transparent inline infix def matchExhaustively(using m: Mirror.SumOf[HkdFor[T, F]])(
        inline matchExpression: HkdFor[T, F] => Any
    ) = ${ matchExhaustivelyImpl[T, F]('self, 'matchExpression, 'm) }

  private def matchExhaustivelyImpl[T: Type, F[_]: Type](
      self: Expr[HkdFor[T, F]],
      expr: Expr[HkdFor[T, F] => Any],
      m: Expr[Mirror.Of[HkdFor[T, F]]]
  )(using q: Quotes): Expr[Any] =
    import q.reflect.{*, given}
    val diagnosticPosition = Position(
      self.asTerm.pos.sourceFile,
      start = expr.asTerm.pos.start - ("matchExhaustively".length + 1),
      end = expr.asTerm.pos.start + 1)

    val expectedCases = m match
      case '{ $m: Mirror.ProductOf[s] } => Seq(TypeRepr.of[com.tschuchort.hkd.HkdFor$package.HkdFor[T, F]])
      case '{
            type elems <: Tuple;
            $m: Mirror.SumOf[s] { type MirroredElemTypes = `elems` }
          } =>
        tupleToTypeReprs[elems]

    val caseDefs = expr.asTerm match
      case Inlined(_,
                   _,
                   TypeApply(
                     Select(
                       Block(
                         List(
                           DefDef(
                             lambdaName,
                             List(TermParamClause(List(ValDef(lambdaParamName, lambdaParamType, _)))),
                             _,
                             Some(Match(matchVar @ Ident(matchVarName), cases))
                           )
                         ),
                         Closure(Ident(closureName), _)
                       ),
                       "$asInstanceOf$"
                     ),
                     _
                   ))
          if closureName == lambdaName && matchVarName == lambdaParamName =>
        cases

      case _ => report.errorAndAbort("Must be a lambda with top-level match expression", expr)

    def computeMatchedType(caseDefPattern: Tree): Seq[TypeRepr] =
      try
        caseDefPattern match
          case Wildcard() => List(TypeRepr.of[Any])

          case Alternatives(patterns) => patterns.flatMap(computeMatchedType)

          case TypedOrTest(_, tpt) =>
            assert(tpt.symbol.isType)
            List(tpt.tpe)

          case Bind(bindName, tr) =>
            assert(tr.symbol.isType)
            List(tr.symbol.typeRef.widenByName)

          case Unapply(fun /*@ Select(Apply(TypeApply(_, typeArgs), _), "unapply")*/, implicits, bindPatterns) =>
            fun.tpe.widenTermRefByName match
              // A MethodType is a regular method taking term parameters, a PolyType is a method taking type parameters,
              // a TypeLambda is a method returning a type and not a value. Unapply's type should be a function with no
              // type parameters, with a single value parameter (the match scrutinee) and with an Option[?] return type
              // (no curried function), thus it should be a MethodType.
              case methodType: MethodType =>
                methodType.resType.asType match
                  // Also matches Some[] and None in an easy way
                  case '[Option[tpe]] => TypeRepr.of[tpe] match
                      case AndType(left, right)
                          if methodType.paramTypes.nonEmpty && left =:= methodType.param(0) => List(right)

                      case AndType(left, right)
                          if methodType.paramTypes.nonEmpty && right =:= methodType.param(0) => List(left)

                      case tpe => List(tpe)

                  case '[tpe] => List(TypeRepr.of[tpe])

              case tpe: TypeRepr => report.errorAndAbort(
                  s"Expected type of Unapply function to be MethodType. Was: ${Printer.TypeReprStructure.show(tpe)}"
                )

          case pattern =>
            report.errorAndAbort(s"Expected pattern of CaseDef to be either Alternative, TypedOrTest, Bind or Unapply. " +
              s"Was: ${Printer.TreeStructure.show(pattern)}")
      catch
        // Better error message for compiler bug. As usual the compiler is leaking internal implementation classes of Type
        // and then failing to match on them. This bug occurs when a CaseDef has a type error.
        case e: MatchError if e.getMessage().contains("dotty.tools.dotc.core.Types$PreviousErrorType") =>
          report.errorAndAbort("Macro could not be executed due to a previous error " +
                                 "in the match expression. Fix other errors first.",
                               diagnosticPosition)

    val caseDefTypes = caseDefs.flatMap { caseDef =>
      if caseDef.guard.isDefined then List()
      else computeMatchedType(caseDef.pattern)
    }

    val uncoveredCases = expectedCases.map(_.asType).filterNot { case '[expectedCase] =>
      caseDefTypes.map(_.asType).exists { case '[caseDefType] =>
        (TypeRepr.of[expectedCase] <:< TypeRepr.of[caseDefType])
        || Expr.summon[expectedCase <:< caseDefType].isDefined
      }
    }

    if uncoveredCases.nonEmpty then
      val casesString = uncoveredCases.map { t =>
        "_: " + Printer.TypeReprCode.show(typeReprOf(t))
      }.mkString(", ")

      report.warning(
        s"Match may not be exhaustive.\n\nIt would fail on case: $casesString",
        diagnosticPosition
      )

    '{ $expr($self) }

  def unapply[T, F[_]](h: HkdFor[T, F])(using m: Mirror.ProductOf[T]): Tuple.Map[m.MirroredElemTypes, F] =
    Tuple.fromProduct(h).asInstanceOf[Tuple.Map[m.MirroredElemTypes, F]]

  // noinspection TypeAnnotation
  inline def applyDynamic[T, F[_]](methodName: "apply")(inline args: Any*) =
    ${ applyDynamicNamedImpl[T, F]('methodName, 'args) }

  // noinspection TypeAnnotation
  inline def applyDynamicNamed[T, F[_]](methodName: "apply")(inline args: (String, Any)*) =
    ${ applyDynamicNamedImpl[T, F]('methodName, 'args) }

  private def applyDynamicNamedImpl[T: Type, F[_]: Type](
      methodNameExpr: Expr[String],
      argsExpr: Expr[Seq[Any | (String, Any)]]
  )(using q: Quotes): Expr[com.tschuchort.hkd.HkdFor$package.HkdFor[T, F]] =
    import q.reflect.*
    import q.reflect.given // superfluous import helps IntelliJ code completion

    requireDynamicMethodName("apply", methodNameExpr, methodOwnerType = TypeRepr.of[this.type])

    val paramNamesTypesValues: Seq[(Option[String], TypeRepr, Expr[Any])] = parseDynamicArgsExpr(argsExpr)

    val expectedParamNamesWithTypes = TypeRepr.of[T].caseFieldsWithTypes.map { case (name, typeRep) =>
      typeRep.asType match
        case '[fieldType] => (name, TypeRepr.of[F[fieldType]])
    }

    val normalizedParams = checkAndNormalizeParams(
      expectedParamNamesWithTypes.map { case (name, tpe) => (name, tpe, /* default */ None) },
      paramNamesTypesValues
    )

    val ctorArgs = Expr.ofSeq(normalizedParams.map { case (name, _, expr) => Expr.ofTuple((Expr(name), expr)) })

    val (tMirror, tClass, tName, fName) =
      Expr.summonAllOrAbort[(Mirror.ProductOf[T], TypeTag[T], TypeName[T], TypeName[F])]

    '{
      new HkdForImpl[T](${ ctorArgs }*)(using $tMirror, $tName, $tClass)
        .asInstanceOf[com.tschuchort.hkd.HkdFor$package.HkdFor[T, F]]
      // ^ When referencing the fully qualified name of an opaque type, the compiler does not seem to resolve it immediately to
      // the RHS even if the opaque type is transparent in this scope. The fully qualified type is "as seen from outside the package".
      // Still, the RHS is inferred at the callsite of a transparent def returning an opaque type, but at least with this trick it
      // will be recognized as =:= to the opaque type.
    }

  class RefinementHelper[T] private ():
    // ^ Note: must be a class and not trait, so that it can be instantiated and cast in quoted code without generating
    // an anonymous class with its own Symbol that would be remembered by the instance.

    /** Contains the refined type generated by the macro for parameters [[T]], [[F]] */
    type Out[F[_]] <: HkdFor[T, F]

  object RefinementHelper:
    /** This function serves to introduce a level of indirection because quoted code can not call the private constructor of
      * [[RefinementHelper]], whereas calling private functions seems to work fine.
      */
    private def indirectlyCallCtor[T]() = new RefinementHelper[T]

    /** This given computes the field type information at compile time through a macro and saves it in [[RefinementHelper.Out]] as
      * a refinement of the structural type [[HkdForImpl]] which is the runtime representation of a generated HKD. The refinement
      * type inside [[RefinementHelper.Out]] is then applied to the runtime type [[HkdForImpl]] by an implicit conversion at the
      * use-site.
      */
    transparent inline given [T]: RefinementHelper[T] = ${ givenRefinementHelperImpl[T] }

    private def givenRefinementHelperImpl[T: Type](using q: Quotes): Expr[RefinementHelper[T]] =
      import q.reflect.*
      import q.reflect.given // superfluous import helps IntelliJ code completion
      try
        val outTypeRepr = TypeLambda(
          List("F"),
          boundsFn = _ =>
            List(
              TypeBounds.upper(TypeLambda(
                List("_"), // Symbol.freshName? Unfortunately still experimental, so I'll hope for the best.
                boundsFn = _ => List(TypeBounds.empty),
                bodyFn = _ => TypeRepr.of[Any]
              ))),
          bodyFn = lambdaF =>
            type F[_]
            given Type[F] = lambdaF.param(0).asType.asInstanceOf

            // Add refinements for case class properties
            TypeRepr.of[T].caseFieldsWithTypes.foldLeft(TypeRepr.of[HkdFor[T, F]]) {
              case (refinementTypeRepr, (fieldName, fieldTypeRepr)) =>
                fieldTypeRepr.asType match
                  case '[fieldType] => Refinement(refinementTypeRepr, fieldName, TypeRepr.of[F[fieldType]])
            }
        )

        type OutGen[F[_]]
        given Type[OutGen] = outTypeRepr.asType.asInstanceOf

        // For some reason quoted code can not call private ctors, but private functions are a-ok!
        '{
          RefinementHelper.indirectlyCallCtor[T]().asInstanceOf[RefinementHelper[T] { type Out[F[_]] = OutGen[F] }]
        }

      catch
        case ex: Throwable =>
          // Exceptions during the expansion of given-macros are swallowed and the given ignored unless the right
          // compiler flags are set, thus we should always print it, too.
          Console.err.println(ex)
          throw ex

  /** An implicit conversion to apply the refinement and thus make field type information available.
    */
  // noinspection ConvertExpressionToSAM
  given applyRefinement[T, F[_]](using
      refinementHelper: RefinementHelper[T]
  ): Conversion[HkdFor[T, F], refinementHelper.Out[F]] = new Conversion:
    override def apply(x: HkdFor[T, F]): refinementHelper.Out[F] = x.asInstanceOf[refinementHelper.Out[F]]

  /** Implicit conversion to apply the refinement to "indirect" subtypes of HkdFor[T, F], such as intersection types that are the
    * result of type tests. Of course HkdFor[T, F] has no real subtypes; the subtype relationships are established with <:<
    * instances, which is why the [[applyRefinement]] conversion can not be chosen automatically and we need this.
    */
  given applyRefinementIndirectSubtype[T, F[_], H](using c: H <:< HkdFor[T, F])(using
      refinementHelper: RefinementHelper[T]
  ): Conversion[H, refinementHelper.Out[F]] = new Conversion:
    override def apply(x: H): refinementHelper.Out[F] = c(x).asInstanceOf[refinementHelper.Out[F]]

  /** For some reason the compiler will complain that `makeFullyAppliedMirror.MirroredElemTypes` is not a constant type if we do
    * not use this indirection to move the Tuple.Map[m.MirroredElemTypes, F] out of the given, despite the fact that the
    * MirroredElemTypes _are_ known. I don't know why.
    */
  trait FullyAppliedProductMirrorHelper[T, F[_]]:
    type MirroredElemTypes <: Tuple
    type FieldCount <: Int
    val fieldCount: FieldCount

  transparent inline given [T, F[_]](using m: Mirror.ProductOf[T]): FullyAppliedProductMirrorHelper[T, F] =
    new FullyAppliedProductMirrorHelper[T, F]:
      override type MirroredElemTypes = Tuple.Map[m.MirroredElemTypes, F]
      override type FieldCount = Tuple.Size[m.MirroredElemTypes]
      override val fieldCount: FieldCount = constValue[FieldCount]

  inline given makeFullyAppliedProductMirror[T, F[_]](using
      m: Mirror.ProductOf[T],
      h: FullyAppliedProductMirrorHelper[T, F],
      tClass: ClassTag[T]
  ): (K0.ProductGeneric[HkdFor[T, F]] & Mirror.ProductOf[HkdFor[T, F]] {
    type Kind = K0.type
    type MirroredElemTypes = h.MirroredElemTypes
    type MirroredElemLabels = m.MirroredElemLabels
    type MirroredLabel = "HkdFor"
    type MirroredType = HkdFor[T, F]
    type MirroredMonoType = HkdFor[T, F]
  }) = new Mirror.Product {
    type Kind = K0.type
    type MirroredType = HkdFor[T, F]
    type MirroredMonoType = HkdFor[T, F]
    type MirroredElemTypes = h.MirroredElemTypes
    type MirroredElemLabels = m.MirroredElemLabels
    type MirroredLabel = "HkdFor"

    override def fromProduct(p: Product): HkdFor[T, F] =
      new HkdForImpl[T](
        Seq.range(0, h.fieldCount).map { i => (p.productElementName(0), p.productElement(i)) }*
      )
  }

  inline given makePartiallyAppliedProductMirror[T](using
      m: Mirror.ProductOf[T],
      tClass: ClassTag[T]
  ): (K11.ProductGeneric[HkdFor_[T]] & Mirror.Product {
    // All of the expected types, particularly MirroredElemTypes and MirroredElemLabels, need to be in the
    // given's public type declaration, otherwise any library (shapeless3) will not be able to match the Tuples because
    // the type will not be a compile-time static type. `transparent inline` can not fix this problem, because the derivation
    // methods that use this Mirror are inline themselves and thus will not benefit from the type narrowing of transparent defs.
    type Kind = K11.type;
    type MirroredType[F[_]] = HkdFor_[T][F];
    type MirroredMonoType = HkdFor_[T][[_] =>> Any];
    type MirroredElemTypes[F[_]] = Tuple.Map[m.MirroredElemTypes, F]
    type MirroredLabel = "HkdFor"
    type MirroredElemLabels = m.MirroredElemLabels
  }) = new Mirror.Product {
    type Kind = K11.type;
    type MirroredType[F[_]] = HkdFor_[T][F];
    type MirroredMonoType = HkdFor_[T][[_] =>> Any];
    type MirroredElemTypes[F[_]] = Tuple.Map[m.MirroredElemTypes, F]
    type MirroredLabel = "HkdFor"
    type MirroredElemLabels = m.MirroredElemLabels
    override def fromProduct(p: Product): HkdFor_[T][[_] =>> Any] =
      new HkdForImpl[T](
        Seq.range(0, constValue[Tuple.Size[m.MirroredElemLabels]])
          .map { i => (p.productElementName(0), p.productElement(i)) }*
      )
  }

  trait FullyAppliedCoproductMirrorHelper[T, F[_]]:
    type MirroredElemTypes <: Tuple
    type CasesCount <: Int
    val casesCount: CasesCount

  transparent inline given [T, F[_]](using m: Mirror.SumOf[T]): FullyAppliedCoproductMirrorHelper[T, F] =
    new FullyAppliedCoproductMirrorHelper[T, F]:
      override type MirroredElemTypes = Tuple.Map[m.MirroredElemTypes, [A] =>> com.tschuchort.hkd.HkdFor$package.HkdFor[A, F]]
      // ^ must use fully qualified name here to prevent dealiasing because we're in a transparent method

      override type CasesCount = Tuple.Size[m.MirroredElemTypes]
      override val casesCount: CasesCount = constValue[CasesCount]

  inline given makeFullyAppliedCoproductMirror[T, F[_]](using
      m: Mirror.SumOf[T],
      h: FullyAppliedCoproductMirrorHelper[T, F],
      casesClassTags: K0.CoproductInstances[TypeTag, T]
  ): (K0.CoproductGeneric[HkdFor[T, F]] & Mirror.SumOf[HkdFor[T, F]] {
    type Kind = K0.type
    type MirroredElemTypes = h.MirroredElemTypes
    type MirroredElemLabels = m.MirroredElemLabels
    type MirroredLabel = "HkdFor"
    type MirroredType = HkdFor[T, F]
    type MirroredMonoType = HkdFor[T, F]
  }) = new Mirror.Sum {
    type Kind = K0.type
    type MirroredType = HkdFor[T, F]
    type MirroredMonoType = HkdFor[T, F]
    type MirroredElemTypes = h.MirroredElemTypes
    type MirroredElemLabels = m.MirroredElemLabels
    type MirroredLabel = "HkdFor"

    override def ordinal(x: MirroredMonoType): Int =
      boundary {
        Seq.range(0, h.casesCount)
          .foreach { i =>
            val caseClassTag: TypeTag[?] = casesClassTags.inject(i)([t] => (classTag: TypeTag[t]) => classTag)
            if x.tClass <:< caseClassTag then
              boundary.break(i)
          }

        throw AssertionError(s"Could not match runtime type of value '${x.toString}'. " +
          s"The case types that I considered were ${showType[m.MirroredElemTypes]}")
      }
  }

  inline given makePartiallyAppliedCoproductMirror[T](using
      m: Mirror.SumOf[T],
      casesClassTags: K0.CoproductInstances[TypeTag, T]
  ): (K11.CoproductGeneric[HkdFor_[T]] & Mirror.Sum {
    // All of the expected types, particularly MirroredElemTypes and MirroredElemLabels, need to be in the
    // given's public type declaration, otherwise any library (shapeless3) will not be able to match the Tuples because
    // the type will not be a compile-time static type. `transparent inline` can not fix this problem, because the derivation
    // methods that use this Mirror are inline themselves and thus will not benefit from the type narrowing of transparent defs.
    type Kind = K11.type;
    type MirroredType[F[_]] = HkdFor_[T][F];
    type MirroredMonoType = HkdFor_[T][[_] =>> Any];
    type MirroredElemTypes[F[_]] = Tuple.Map[m.MirroredElemTypes, [A] =>> com.tschuchort.hkd.HkdFor$package.HkdFor[A, F]]
    type MirroredLabel = "HkdFor"
    type MirroredElemLabels = m.MirroredElemLabels
  }) = new Mirror.Sum {
    type Kind = K11.type;
    type MirroredType[F[_]] = HkdFor_[T][F];
    type MirroredMonoType = HkdFor_[T][[_] =>> Any];
    type MirroredElemTypes[F[_]] = Tuple.Map[m.MirroredElemTypes, [A] =>> com.tschuchort.hkd.HkdFor$package.HkdFor[A, F]]
    type MirroredLabel = "HkdFor"
    type MirroredElemLabels = m.MirroredElemLabels
    override def ordinal(x: MirroredMonoType): Int =
      boundary {
        Seq.range(0, constValue[Tuple.Size[m.MirroredElemLabels]])
          .foreach { i =>
            val caseClassTag: TypeTag[?] = casesClassTags.inject(i)([t] => (classTag: TypeTag[t]) => classTag)
            if x.tClass <:< caseClassTag then
              boundary.break(i)
          }

        throw AssertionError(s"Could not match runtime type of value '${x.toString}'. " +
          s"The case types that I considered were ${showType[m.MirroredElemTypes]}")
      }
  }

  /** TypeTag used to make runtime type checks and hide the implementation for future compatibility. (Can not be an opaque alias
    * because we need wildcards)
    */
  class TypeTag[T] private (private val impl: izumi.reflect.Tag[T]) extends AnyVal:
    infix def <:<(tt: TypeTag[?]): Boolean = impl <:< tt.impl

  object TypeTag:
    /** Indirection method to work around restriction: inline method can not directly call private ctor */
    private def indirectlyCallCtor[T](impl: izumi.reflect.Tag[T]) = TypeTag(impl)
    inline given [T]: com.tschuchort.hkd.HkdFor.TypeTag[T] = indirectlyCallCtor(izumi.reflect.Tag.apply[T])

/** The runtime representation of a generated HKD. Compile-time information about the fields that this structural type contains at
  * runtime is not available by itself. Instead, it is added later through an implicit conversion to a refinement type of
  * [[HkdForImpl]] with the help of a transparent inline given, which can compute the refinement type at compile-time via a macro.
  */
transparent private class HkdForImpl[+T](elems: (String, Any)*)(using
    m: Mirror.ProductOf[T],
    tName: TypeName[T],
    val tClass: HkdFor.TypeTag[? <: T]
) extends Selectable, Product, Dynamic:
  type Underlying <: T
  private type UnderlyingFields = m.MirroredElemTypes
  private type UnderlyingLabels = m.MirroredElemLabels

  private val fields = Array.from(elems.map(_._2))

  override def canEqual(that: Any): Boolean = that match
    case that: HkdForImpl[?] => (that.tClass == this.tClass)
    case _                   => false

  override def equals(that: Any): Boolean = that match
    case that: HkdForImpl[?] => (that.tClass == this.tClass) && (that.fields sameElements this.fields)
    case _                   => false

  override def productArity: Int = fields.length
  override def productElement(n: Int): Any = fields(n)

  override def toString = s"HkdFor[${tName.value}, ?](${fields.mkString(", ")})"

object HkdForImpl:
  extension [T](self: HkdForImpl[T])
    // This has to be an extension and can not be an instance method due to compiler bug https://github.com/scala/scala3/issues/15413
    inline def selectDynamic(name: String)(using m: Mirror.ProductOf[T]): Any = ${ selectDynamicImpl[T]('self, 'name, 'm) }

  private def selectDynamicImpl[T: Type](using
      q: Quotes)(self: Expr[HkdForImpl[T]], name: Expr[String], m: Expr[Mirror.ProductOf[T]]): Expr[Any] =
    import q.reflect.{*, given}

    val fieldNames = m match
      case '{
            type elems <: Tuple;
            $m: Mirror.ProductOf[s] { type MirroredElemLabels = `elems` }
          } =>
        tupleToTypeReprs[elems].map {
          case ConstantType(StringConstant(fieldName)) => fieldName
          case t => throw AssertionError(s"Expected MirroredElemLabel of ${showType[T]} to be a String constant. " +
              s"Was: ${Printer.TypeReprStructure.show(t)}")
        }

    fieldNames.indexOf(name.valueOrAbort) match
      case -1 => report.errorAndAbort(s"No such field: $name", name)
      case i  => '{ $self.fields(${ Expr(i) }) }
