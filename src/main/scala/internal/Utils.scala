package com.tschuchort.hkd.internal

import scala.util.chaining.*
import scala.util.boundary
import scala.annotation.{experimental, nowarn, targetName}
import scala.collection.IndexedSeqView
import scala.collection.mutable
import scala.compiletime.*
import scala.deriving.Mirror
import scala.quoted.*
import cats.implicits.*
import cats.Functor
import scala.quoted.runtime.StopMacroExpansion
import scala.annotation.tailrec
import scala.annotation.implicitNotFound
import scala.Tuple.InverseMap
import shapeless3.deriving.K0

transparent inline def inspectTree(inline expr: Any): Any = ${ inspectTreeImpl('expr) }

private def inspectTreeImpl(expr: Expr[Any])(using q: Quotes): Expr[Any] =
  import q.reflect.*
  printTastyTree(expr.asTerm)
  expr

/** Dealiases the type and all its arguments, recursively. */
def dealiasNested(using q: Quotes)(tpe: q.reflect.TypeRepr): q.reflect.TypeRepr =
  import q.reflect.{*, given}
  tpe match
    case AppliedType(tycon, args) => AppliedType(dealiasNested(tycon), args.map(dealiasNested(_)))
    case _                        => tpe.dealias

/** Records the types of all leafs (case classes, case objects, enum cases) of a deep ADT hierarchy that may contain multiple
  * levels of sealed traits.
  */
trait AdtHierarchyLeafs[T] { type MirroredLeafTypes <: Tuple }

transparent inline given [T]: AdtHierarchyLeafs[T] = ${ deriveAdtLeafsImpl[T] }

private def deriveAdtLeafsImpl[T: Type](using q: Quotes): Expr[AdtHierarchyLeafs[T]] =
  import q.reflect.{*, given}

  def gatherLeafs(s: TypeRepr): Seq[TypeRepr] = s.asType match
    case '[s] =>
      Expr.summonOrAbort[Mirror.Of[s]] match
        case '{ $m: Mirror.ProductOf[s] } =>
          Seq(TypeRepr.of[s])
        case '{
              type elems <: Tuple;
              $m: Mirror.SumOf[s] { type MirroredElemTypes = `elems` }
            } =>
          tupleToTypeReprs[elems].foldLeft(Seq.empty[TypeRepr]) { case (acc, elemTpr) =>
            acc ++ gatherLeafs(elemTpr)
          }

  type Leafs <: Tuple
  given Type[Leafs] = tupleOfTypeReprs(gatherLeafs(TypeRepr.of[T])).asType.asInstanceOf

  '{ new AdtHierarchyLeafs[T] { override type MirroredLeafTypes = Leafs } }

extension (b1: Boolean) infix def implies(b2: Boolean): Boolean = !b1 || b2

extension [T](s: IndexedSeq[T])
  def movingWindow(windowSize: Int): Seq[IndexedSeqView[T]] =
    require(windowSize >= 1)
    val sLength = s.length
    List.unfold(0) { currentIndex =>
      if currentIndex <= sLength - 1 then
        Some(
          (
            IndexedSeqView.Slice(s, currentIndex, Math.max(currentIndex + windowSize, sLength - 1)),
            currentIndex + 1
          )
        )
      else None
    }

extension [A](s: Seq[A])
  /** Checks whether all the elements in the sequence are distinct from each other by [[f]] */
  def allDistinctBy[B](f: A => B): Boolean = s.distinctBy(f).length == s.length

extension [A](aas: Seq[A])
  /** Matches the elements in [[aas]] with the elements in [[bs]] according to the key function. The order of [[aas]] will be
    * maintained, optionally appending an additional [[None]] element at the end of the list to contain all the elements in [[bs]]
    * that did not have a corresponding match in [[aas]]. Each sequence of [[B]] matches for an [[A]] is in the order that they
    * appeared in the [[bs]] list.
    */
  def matchBy[B, K](bs: Seq[B])(byA: A => K)(byB: B => K): Seq[(Option[A], Seq[B])] =
    val unmatchedBs = new mutable.HashMap[K, mutable.ListBuffer[B]](
      bs match {
        case _: IndexedSeq[?] => bs.length // Only when indexed, to avoid traversing the Seq
        case _                => mutable.HashMap.defaultInitialCapacity
      },
      mutable.HashMap.defaultLoadFactor
    ).tap { m =>
      bs.foreach { b =>
        m.updateWith(key = byB(b)) {
          case Some(otherBsForKey) => Some(otherBsForKey.appended(b))
          case None                => Some(mutable.ListBuffer(b))
        }
      }
    }

    (for (a <- aas)
      // Note: this MUST be executed before the concat operation, or else the result will be wrong because
      // [[unmatchedBs]] is mutable!
      yield (Some(a), unmatchedBs.remove(byA(a)).map(_.toList).getOrElse(Seq.empty)))
      ++ {
        val leftovers = unmatchedBs.iterator.flatMap { case (_, bsForKey) => bsForKey }.toSeq
        leftovers match {
          case Seq()     => Seq.empty[(Option[A], Seq[B])]
          case leftovers => Seq((Option.empty[A], leftovers))
        }
      }

extension [CC[_]: Functor, A](coll: CC[A])
  /** Applies the partial function to every argument to narrow the type, but instead of dropping unmatched elements like
    * [[Seq.collect]], returns `None` for the entire list.
    */
  def collectAllOrNone[B](pf: PartialFunction[A, B]): Option[CC[B]] =
    boundary {
      Some(coll.map { x =>
        pf.applyOrElse(x, { _ => boundary.break(None) })
      })
    }

/** Functional composition of two type functions */
@targetName("Compose")
private[tschuchort] infix type `.`[F[_], G[_]] = [A] =>> F[G[A]]

@targetName("Product")
private[tschuchort] infix type `*`[F[_], G[_]] = [A] =>> (F[A], G[A])

private def printTypeDealiasedImpl[T: Type](using q: Quotes): Expr[Unit] = {
  import q.reflect.*
  println("dealiased: " + TypeRepr.of[T].dealias.show)
  '{ () }
}

inline def printTypeDealiased[T]: Unit = ${ printTypeDealiasedImpl[T] }

trait TypeName[T <: AnyKind]:
  val value: String

object TypeName:
  transparent inline given [T <: AnyKind]: TypeName[T] = ${ givenTypeNameImpl[T] }

  private def givenTypeNameImpl[T <: AnyKind: Type](using q: Quotes): Expr[TypeName[T]] =
    import q.reflect.{*, given}

    // Removes redundant lambda expressions. ONLY SAFE FOR GETTING THE NAME. The resulting TypeRepr can not generally be used
    // in a position that expects * -> * kind.
    @tailrec def etaReduceForName(t: TypeRepr): TypeRepr =
      t match
        case tl @ TypeLambda(paramNames, paramBounds, AppliedType(applied, appliedArgs))
            if paramNames.size == appliedArgs.size
              && appliedArgs.zipWithIndex.forall { case (ParamRef(binder, paramIndex), i) =>
                binder == tl && paramIndex == i
              } =>
          etaReduceForName(applied)
        case t => t

    val name: String =
      Printer.TypeReprShortCode
        .show(
          etaReduceForName(TypeRepr.of[T]).widen.widenTermRefByName.simplified
        )
        .replace(" >: Nothing", "")
        .replace(" <: Any", "")
        .replaceAll("_\\$\\d+", "_") match
        case s"[$paramList] =>> $rhs" if paramList == rhs => rhs
        case s                                            => s

    '{ new TypeName[T] { val value: String = ${ Expr(name) } } }

enum ShowTypeOptions:
  case ShortName, FqName, Widen, WidenByName, WidenTermRefByName, Simplified

private given FromExpr[ShowTypeOptions] with
  def unapply(expr: Expr[ShowTypeOptions])(using Quotes): Option[ShowTypeOptions] =
    import quotes.reflect.*
    expr match
      case '{ ShowTypeOptions.ShortName }          => Some(ShowTypeOptions.ShortName)
      case '{ ShowTypeOptions.FqName }             => Some(ShowTypeOptions.FqName)
      case '{ ShowTypeOptions.Widen }              => Some(ShowTypeOptions.Widen)
      case '{ ShowTypeOptions.WidenByName }        => Some(ShowTypeOptions.WidenByName)
      case '{ ShowTypeOptions.WidenTermRefByName } => Some(ShowTypeOptions.WidenTermRefByName)
      case '{ ShowTypeOptions.Simplified }         => Some(ShowTypeOptions.Simplified)
      case _                                       => None

inline def showType[T](inline options: ShowTypeOptions*): String & scala.Singleton =
  ${ showTypeImpl[T]('options) }

inline def showType[T]: String & scala.Singleton =
  ${ showTypeImpl[T]('{ Seq(ShowTypeOptions.ShortName) }) }

private def showTypeImpl[T: Type](optionsExpr: Expr[Seq[ShowTypeOptions]])(using q: Quotes): Expr[String & scala.Singleton] =
  import q.reflect.*
  import ShowTypeOptions.*

  val options = optionsExpr.valueOrAbort

  def requireExactlyOneOption(subset: Seq[ShowTypeOptions]): Unit =
    require(options.count(subset.contains(_)) == 1,
            s"'options' must contain exactly one of ${subset.map { _.getClass.getSimpleName }.mkString(", ")}")

  requireExactlyOneOption(Seq(ShortName, FqName))

  def applyOption(tpe: TypeRepr, opt: ShowTypeOptions) = opt match
    case ShortName          => tpe
    case FqName             => tpe
    case Widen              => tpe.widen
    case WidenByName        => tpe.widenByName
    case WidenTermRefByName => tpe.widenTermRefByName
    case Simplified         => tpe.simplified

  val modifiedTpe = options.foldLeft(TypeRepr.of[T])(applyOption)

  if options.contains(ShortName) then Expr(Printer.TypeReprShortCode.show(modifiedTpe).asInstanceOf[String & scala.Singleton])
  else if options.contains(FqName) then Expr(Printer.TypeReprCode.show(modifiedTpe).asInstanceOf[String & scala.Singleton])
  else throw AssertionError("At least one name option must be given!")

private def printTypeDefImpl[T: Type](using q: Quotes): Expr[Unit] = {
  import q.reflect.*
  println("Print type def: " + TypeRepr.of[T].typeSymbol.tree.show)
  '{ () }
}

inline def printTypeDef[A]: Unit = ${ printTypeDefImpl[A] }

inline def labelsOf[A](using p: Mirror.ProductOf[A]): p.MirroredElemLabels =
  constValueTuple[p.MirroredElemLabels]

@nowarn("msg=discarded expression")
private def indentTreeStr(s: String): String = {
  val o = new StringBuilder()
  val indentSize = 2
  var indentLevel = 0
  var skipNextSpaces = false

  def newLine(): Unit =
    o.append('\n')
    o.appendAll(Array.fill[Char](indentSize * indentLevel)(' '))

  val lastIndex = s.length - 1
  for (i <- 0 to lastIndex)
    if s(i) == '(' && i < lastIndex && s(i + 1) != ')' then
      indentLevel += 1
      o.append(s(i))
      newLine()
    else if s(i) == ')' && i != 0 && s(i - 1) != '(' then
      indentLevel -= 1
      o.append(s(i))
    else if s(i) == ',' then
      o.append(',')
      newLine()
      skipNextSpaces = true
    else if s(i) == ' ' && skipNextSpaces then ()
    else
      o.append(s(i))
      skipNextSpaces = false

  o.result()
}

def printTastyTree(using q: Quotes)(tree: q.reflect.Tree): Unit = {
  import q.reflect.*
  println(indentTreeStr(Printer.TreeStructure.show(tree)))
}

def printTastyTypeRepr(using q: Quotes)(typeRepr: q.reflect.TypeRepr): Unit = {
  import q.reflect.*
  println(indentTreeStr(Printer.TypeReprStructure.show(typeRepr)))
}

extension (e: Expr.type)
  def summonOrErrorMsg[T](using Type[T])(using Quotes): Either[String, Expr[T]] = {
    import quotes.reflect.*
    Implicits.search(TypeRepr.of[T]) match {
      case iss: ImplicitSearchSuccess => Right(iss.tree.asExpr.asInstanceOf[Expr[T]])
      case isf: ImplicitSearchFailure => Left(isf.explanation)
    }
  }

extension (e: Expr.type)
  def summonOrAbort[T](using Type[T])(using q: Quotes): Expr[T] = summonOrAbort(errPos = q.reflect.Position.ofMacroExpansion)

  def summonOrAbort[T](using Type[T])(using q: Quotes)(errPos: q.reflect.Position): Expr[T] =
    import q.reflect.*
    Implicits.search(TypeRepr.of[T]) match {
      case iss: ImplicitSearchSuccess => iss.tree.asExpr.asInstanceOf[Expr[T]]
      case isf: ImplicitSearchFailure => report.errorAndAbort(isf.explanation, errPos)
    }

extension (e: Expr.type)
  inline def summonAllOrAbort[T <: Tuple](using Type[T])(using q: Quotes): Tuple.Map[T, Expr] =
    summonAllOrAbort(errPos = q.reflect.Position.ofMacroExpansion)

  inline def summonAllOrAbort[T <: Tuple](using Type[T])(using q: Quotes)(
      errPos: q.reflect.Position
  ): Tuple.Map[T, Expr] =
    import q.reflect.{*, given}

    inline erasedValue[T] match
      case _: EmptyTuple => EmptyTuple
      case _: (t *: ts) =>
        Implicits.search(TypeRepr.of[t]) match
          case iss: ImplicitSearchSuccess =>
            iss.tree.asExpr.asExprOf[t] *: Expr.summonAllOrAbort[ts](errPos)
          case isf: ImplicitSearchFailure =>
            report.errorAndAbort(isf.explanation, errPos)

object ImplicitsPriority:
  open class L1
  object L1 { given L1() }

  open class L2 extends L1
  object L2 { given L2() }

  open class L3 extends L2
  object L3 { given L3() }

  open class L4 extends L3
  object L4 { given L4() }

  open class L5 extends L4
  object L5 { given L5() }

/** Use this class when getting errors about irreducable match expressions with `Tuple.Map[Tuple.InverseMap[...]]` and vice versa.
  * Example:
  * {{{
  * import AssumeInjective.given
  * given AssumeInjective[F] with {}
  * }}}
  */
class AssumeInjective[F[_]]
object AssumeInjective:
  given [S <: Tuple, F[_]](using
      AssumeInjective[F] @implicitNotFound(
        "Write `import AssumeInjective.given; given AssumeInjective[${F}] with {}` if you can guarantee that `${F}` is injective")
  ): (S =:= Tuple.Map[Tuple.InverseMap[S, F], F]) = `<:<`.refl[Unit].asInstanceOf

  given [S <: Tuple, F[_]](using
      AssumeInjective[F] @implicitNotFound(
        "Write `import AssumeInjective.given; given AssumeInjective[${F}] with {}` if you can guarantee that `${F}` is injective")
  ): (Tuple.InverseMap[Tuple.Map[S, F], F] =:= S) = `<:<`.refl[Unit].asInstanceOf

  /** This given tends to have a bad impact on compilation time, so import it only in a small scope if possible */
  given [A, B, F[_]](using A =:= B): (F[A] =:= F[B]) = `<:<`.refl[Unit].asInstanceOf

def typeIdentOf[T <: AnyKind](using q: Quotes)(using Type[T]) =
  import q.reflect.*
  TypeIdent(TypeRepr.of[T].typeSymbol)

def typeReprOf(using q: Quotes)(tpe: Type[?]): q.reflect.TypeRepr =
  tpe match { case '[tpe] => q.reflect.TypeRepr.of[tpe] }

def isTuple(using q: Quotes)(tpr: q.reflect.TypeRepr): Boolean =
  tpr.asType match {
    case '[EmptyTuple] => true
    case '[t *: ts]    => true // '[_ *: _] causes compiler error but '[t *: ts] works
    case _             => false
  }

def tupleToTypeReprs[T <: Tuple: Type](using q: Quotes): Seq[q.reflect.TypeRepr] =
  import q.reflect.{*, given}
  Type.of[T] match
    case '[head *: tail] => TypeRepr.of[head] +: tupleToTypeReprs[tail]
    case '[EmptyTuple]   => Seq.empty

def tupleToTypes[T <: Tuple: Type](using q: Quotes): Seq[Type[? <: Tuple.Union[T]]] =
  tupleToTypeReprs[T].map(_.asType.asInstanceOf[Type[? <: Tuple.Union[T]]])

def tupleOfTypes(using q: Quotes)(tpes: Seq[Type[?]]): Type[? <: Tuple] =
  import q.reflect.{*, given}

  tpes.foldRight[Type[? <: Tuple]](Type.of[EmptyTuple]) { case ('[tpe], acc) =>
    type acc <: Tuple
    given Type[acc] = acc.asInstanceOf[Type[acc]]
    Type.of[tpe *: acc] // foldRight --> prepend; foldLeft --> append
  }

def tupleOfTypeReprs(using q: Quotes)(tpes: Seq[q.reflect.TypeRepr]): q.reflect.TypeRepr =
  import q.reflect.{*, given}
  typeReprOf(tupleOfTypes(tpes.map(_.asType)))

def noTypeBoundsRepr(using q: Quotes) =
  import q.reflect.*
  TypeBounds(TypeRepr.of[Nothing], TypeRepr.of[Any])

def noTypeBoundsTree(using q: Quotes) =
  import q.reflect.*
  TypeBoundsTree(Inferred(TypeRepr.of[Nothing]), Inferred(TypeRepr.of[Any]))

def typeBoundsTreeOf[Lower, Upper](using q: Quotes)(using Lower <:< Upper, Type[Lower], Type[Upper]) =
  import q.reflect.*
  TypeBoundsTree(TypeIdent(TypeRepr.of[Lower].typeSymbol), TypeIdent(TypeRepr.of[Upper].typeSymbol))

def lowerTypeBoundTree[Lower](using q: Quotes)(using Type[Lower]) =
  import q.reflect.*
  TypeBoundsTree(TypeIdent(TypeRepr.of[Lower].typeSymbol), Inferred(TypeRepr.of[Any]))

def upperTypeBoundTree[Upper](using q: Quotes)(using Type[Upper]) =
  import q.reflect.*
  TypeBoundsTree(Inferred(TypeRepr.of[Nothing]), TypeIdent(TypeRepr.of[Upper].typeSymbol))

def refinementOf(using q: Quotes)(baseType: q.reflect.TypeRepr, fields: (String, q.reflect.TypeRepr)*) =
  import q.reflect.*
  fields.foldLeft(baseType) { case (prev, (fieldName, fieldType)) =>
    Refinement(prev, fieldName, fieldType)
  }

extension (using q: Quotes)(tpe: q.reflect.TypeRepr)
  /** Case class fields zipped with their global TypeRepr */
  def caseFieldsWithTypes: List[(String, q.reflect.TypeRepr)] =
    import q.reflect.*
    tpe.typeSymbol.caseFields.map { symbol =>
      (symbol.name, tpe.memberType(symbol).typeSymbol.pipe(TypeIdent.apply).tpe)
    }

extension (using q: Quotes)(tpe: q.reflect.TypeRepr)
  /** TypeReprs of child classes */
  @targetName("TypeReprChildrenTypes")
  def childrenTypes: List[q.reflect.TypeRepr] =
    import q.reflect.*
    tpe.typeSymbol.children.map { cs => TypeTree.ref(cs).tpe }

extension (using q: Quotes)(typeSymbol: q.reflect.Symbol)
  /** TypeReprs of child classes */
  @targetName("symbolChildrenTypes")
  def childrenTypes: List[q.reflect.TypeRepr] =
    import q.reflect.*
    assert(typeSymbol.isType)
    typeSymbol.children.map { cs => TypeTree.ref(cs).tpe }

def requireDynamicMethodName(using q: Quotes)(
    expectedName: String,
    name: Expr[String],
    methodOwnerType: q.reflect.TypeRepr
): Unit =
  import q.reflect.*
  require(expectedName.nonEmpty)
  name.value match
    case Some(`expectedName`) => ()
    case Some(name)           => report.errorAndAbort(s"'${name}' is not a member of ${methodOwnerType.widenTermRefByName.show}")
    case None                 => report.errorAndAbort(s"Invalid method invocation on ${methodOwnerType.widenTermRefByName.show}")

def parseDynamicArgsExpr(using q: Quotes)(
    argsExpr: Expr[Seq[Any | (String, Any)]],
    generalErrorPos: q.reflect.Position = q.reflect.Position.ofMacroExpansion
): Seq[(Option[String], q.reflect.TypeRepr, Expr[Any])] =
  import q.reflect.*

  val args = argsExpr match
    case Varargs(args) => args
    case _             => report.errorAndAbort("Macro internal error: Expected explicit varargs sequence", generalErrorPos)

  args.map {
    case '{ (${ labelExpr }: String, $valueExpr) } =>
      // Widen valueExpr TypeRepr to get rid of Singleton types of String expressions.
      // Note: In applyDynamic if some parameters have names and others do not, those
      // without names will have the name "" (empty String).
      (Some(labelExpr.valueOrAbort).filter(_.nonEmpty), valueExpr.asTerm.tpe.widen, valueExpr)

    // "label" -> value;
    case '{ ArrowAssoc(${ labelExpr }: String).->(${ valueExpr }) } =>
      // Widen valueExpr TypeRepr to get rid of Singleton types of String expressions
      (Some(labelExpr.valueOrAbort).filter(_.nonEmpty), valueExpr.asTerm.tpe.widen, valueExpr)

    case expr =>
      // Widen valueExpr TypeRepr to get rid of Singleton types of String expressions
      (None, expr.asTerm.tpe.widen, expr)
  }

/** Checks that supplied parameters match the expected parameters in type and either name or position. The result is a normalized
  * list of all expected arguments in the same order of [[expectedParamNamesTypesDefaults]] with name, widened argument types and
  * argument expression or default argument expression.
  *
  * @param expectedParamNamesTypesDefaults
  *   Tuples of parameter's expected name, expected type and optional default argument expression.
  * @param paramNamesTypesValues
  *   Tuples of argument's name (if present), argument type and argument expression
  * @param generalErrorPos
  *   Source position to show in errors that can not be traced to a single argument expression, i.e. a missing argument. Default
  *   is the position of macro expansion, which will usually highlight the entire call-site. Alternatively, you may set
  *   {{{
  *   generalErrorPos = argsExpr.asTerm.pos
  *   }}}
  *   where `argsExpr` is the `Expr[Seq[Any]]` you get from `applyDynamic`, to only highlight the argument list.
  * @return
  *   Tuple of name, argument type, argument expression.
  */
def checkAndNormalizeParams(using q: Quotes)(
    expectedParamNamesTypesDefaults: Seq[(String, q.reflect.TypeRepr, Option[Expr[Any]])],
    paramNamesTypesValues: Seq[(Option[String], q.reflect.TypeRepr, Expr[Any])],
    generalErrorPos: q.reflect.Position = q.reflect.Position.ofMacroExpansion
): Seq[(String, q.reflect.TypeRepr, Expr[Any])] =
  import q.reflect.*

  require(expectedParamNamesTypesDefaults.allDistinctBy(_._1), "expected parameters must be distinct by name")

  paramNamesTypesValues.collectAllOrNone { case (Some(name), tpe, value) => (name, tpe, value) } match
    case Some(paramNamesTypesValues) =>
      // Case 1: All params have names and they match exactly (no leftovers) in name and type to the
      // expected params in any order.
      expectedParamNamesTypesDefaults
        .matchBy(paramNamesTypesValues)(_._1 /* name */ )(_._1 /* name */ )
        .map {
          // Parameters that appeared in the call but had no matching name in expected parameters
          case (None, unmatchedParams) =>
            assert(unmatchedParams.nonEmpty)
            unmatchedParams.foreach { case (name, _, expr) =>
              report.error(s"Method does not have a parameter '${name}'", expr)
            }
            throw StopMacroExpansion()

          // Expected param has no param with matching name
          case (Some((name, expectedType, default)), Seq()) =>
            default match
              case Some(default) => (name, expectedType, default)
              case None          => report.errorAndAbort(s"Missing argument for parameter '$name'", generalErrorPos)

          // Exactly one param matching the name of expected param
          case (Some((expectedName, expectedType, default)), Seq(param @ (name: String, paramType, paramValue))) =>
            assert(expectedName == name)
            if paramType <:< expectedType
            then param
            else
              report.errorAndAbort(s"Found:    ${Printer.TypeReprCode.show(paramType)}\n" +
                                     s"Required: ${Printer.TypeReprCode.show(expectedType)}",
                                   paramValue)

          // Note: Scala allows a name to appear multiple times in the parameter list!
          case (Some((name, tpe, default)), matchedParams) =>
            assert(matchedParams.length > 1)
            matchedParams.foreach { case (name, _, expr) =>
              report.error(s"Parameter '$name' may not appear more than once", expr)
            }
            throw StopMacroExpansion()
        }

    case None =>
      // Case 2: Some or no params have names. All params match exactly (no leftovers) the type of the
      // expected param at same position. Those that do have names, also match in name.
      expectedParamNamesTypesDefaults.map(Option(_)).zipAll(paramNamesTypesValues.map(Option(_)), None, None).map {
        case (None, None) => throw AssertionError("impossible match")
        case (Some((expectedName, expectedType, default)), None) =>
          default match
            case Some(default) => (expectedName, expectedType, default)
            case None          => report.errorAndAbort(s"Missing argument for parameter '$expectedName'", generalErrorPos)
        case (None, Some((name, tpe, value))) =>
          report.errorAndAbort(s"Unexpected argument", value)
        case (Some((expectedName, expectedType, default)), Some((maybeName, tpe, value))) =>
          if !(tpe <:< expectedType) then
            report.errorAndAbort(s"Found:    ${Printer.TypeReprCode.show(tpe)}\n" +
                                   s"Required: ${Printer.TypeReprCode.show(expectedType)}",
                                 value)

          maybeName match
            case Some(name) if name != expectedName =>
              report.errorAndAbort(s"Expected parameter of name '$expectedName'", value)
            case _ => ()

          (expectedName, tpe, value)
      }
