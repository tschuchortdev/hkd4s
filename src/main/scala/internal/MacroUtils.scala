package com.tschuchort.hkd
package internal

import scala.annotation.{nowarn, targetName}
import scala.compiletime.{constValueTuple, erasedValue}
import scala.deriving.Mirror
import scala.quoted.*
import scala.quoted.runtime.StopMacroExpansion
import scala.quoted.{Expr, Quotes, Type}
import scala.util.chaining.*

/** Dealiases the type and all its arguments, recursively. */
protected[tschuchort] def dealiasNested(using q: Quotes)(tpe: q.reflect.TypeRepr): q.reflect.TypeRepr =
  import q.reflect.{*, given}
  tpe match
    case AppliedType(tycon, args) => AppliedType(dealiasNested(tycon), args.map(dealiasNested(_)))
    case _                        => tpe.dealias

private def printTypeDealiasedImpl[T: Type](using q: Quotes): Expr[Unit] = {
  import q.reflect.*
  println("dealiased: " + TypeRepr.of[T].dealias.show)
  '{ () }
}

protected[tschuchort] inline def printTypeDealiased[T]: Unit = ${ printTypeDealiasedImpl[T] }

private def printTypeDefImpl[T: Type](using q: Quotes): Expr[Unit] = {
  import q.reflect.*
  println("Print type def: " + TypeRepr.of[T].typeSymbol.tree.show)
  '{ () }
}

protected[tschuchort] inline def printTypeDef[A]: Unit = ${ printTypeDefImpl[A] }

protected[tschuchort] inline def labelsOf[A](using p: Mirror.ProductOf[A]): p.MirroredElemLabels =
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

protected[tschuchort] def printTastyTree(using q: Quotes)(tree: q.reflect.Tree): Unit = {
  import q.reflect.*
  println(indentTreeStr(Printer.TreeStructure.show(tree)))
}

protected[tschuchort] def printTastyTypeRepr(using q: Quotes)(typeRepr: q.reflect.TypeRepr): Unit = {
  import q.reflect.*
  println(indentTreeStr(Printer.TypeReprStructure.show(typeRepr)))
}

extension (e: Expr.type)
  protected[tschuchort] def summonOrErrorMsg[T](using Type[T])(using q: Quotes): Either[String, Expr[T]] = {
    import q.reflect.*
    Implicits.search(TypeRepr.of[T]) match {
      case iss: ImplicitSearchSuccess => Right(iss.tree.asExpr.asInstanceOf[Expr[T]])
      case isf: ImplicitSearchFailure => Left(isf.explanation)
    }
  }

extension (e: Expr.type)
  protected[tschuchort] def summonOrAbort[T](using Type[T])(using q: Quotes): Expr[T] =
    summonOrAbort(errPos = q.reflect.Position.ofMacroExpansion)

  protected[tschuchort] def summonOrAbort[T](using Type[T])(using q: Quotes)(errPos: q.reflect.Position): Expr[T] =
    import q.reflect.*
    Implicits.search(TypeRepr.of[T]) match {
      case iss: ImplicitSearchSuccess => iss.tree.asExpr.asInstanceOf[Expr[T]]
      case isf: ImplicitSearchFailure => report.errorAndAbort(isf.explanation, errPos)
    }

extension (e: Expr.type)
  protected[tschuchort] inline def summonAllOrAbort[T <: Tuple](using Type[T])(using q: Quotes): Tuple.Map[T, Expr] =
    summonAllOrAbort(errPos = q.reflect.Position.ofMacroExpansion)

  protected[tschuchort] inline def summonAllOrAbort[T <: Tuple](using Type[T])(using q: Quotes)(
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

protected[tschuchort] def typeIdentOf[T <: AnyKind](using q: Quotes)(using Type[T]) =
  import q.reflect.*
  TypeIdent(TypeRepr.of[T].typeSymbol)

protected[tschuchort] def typeReprOf(using q: Quotes)(tpe: Type[?]): q.reflect.TypeRepr =
  tpe match { case '[tpe] => q.reflect.TypeRepr.of[tpe] }

protected[tschuchort] def isTuple(using q: Quotes)(tpr: q.reflect.TypeRepr): Boolean =
  tpr.asType match {
    case '[EmptyTuple] => true
    case '[t *: ts]    => true // '[_ *: _] causes compiler error but '[t *: ts] works
    case _             => false
  }

protected[tschuchort] def tupleToTypeReprs[T <: Tuple: Type](using q: Quotes): Seq[q.reflect.TypeRepr] =
  import q.reflect.{*, given}
  Type.of[T] match
    case '[head *: tail] => TypeRepr.of[head] +: tupleToTypeReprs[tail]
    case '[EmptyTuple]   => Seq.empty

protected[tschuchort] def tupleToTypes[T <: Tuple: Type](using q: Quotes): Seq[Type[? <: Tuple.Union[T]]] =
  tupleToTypeReprs[T].map(_.asType.asInstanceOf[Type[? <: Tuple.Union[T]]])

protected[tschuchort] def tupleOfTypes(using q: Quotes)(tpes: Seq[Type[?]]): Type[? <: Tuple] =
  import q.reflect.{*, given}

  tpes.foldRight[Type[? <: Tuple]](Type.of[EmptyTuple]) { case ('[tpe], acc) =>
    type acc <: Tuple
    given Type[acc] = acc.asInstanceOf[Type[acc]]
    Type.of[tpe *: acc] // foldRight --> prepend; foldLeft --> append
  }

protected[tschuchort] def tupleOfTypeReprs(using q: Quotes)(tpes: Seq[q.reflect.TypeRepr]): q.reflect.TypeRepr =
  import q.reflect.{*, given}
  typeReprOf(tupleOfTypes(tpes.map(_.asType)))

protected[tschuchort] def noTypeBoundsRepr(using q: Quotes) =
  import q.reflect.*
  TypeBounds(TypeRepr.of[Nothing], TypeRepr.of[Any])

protected[tschuchort] def noTypeBoundsTree(using q: Quotes) =
  import q.reflect.*
  TypeBoundsTree(Inferred(TypeRepr.of[Nothing]), Inferred(TypeRepr.of[Any]))

protected[tschuchort] def typeBoundsTreeOf[Lower, Upper](using q: Quotes)(using Lower <:< Upper, Type[Lower], Type[Upper]) =
  import q.reflect.*
  TypeBoundsTree(TypeIdent(TypeRepr.of[Lower].typeSymbol), TypeIdent(TypeRepr.of[Upper].typeSymbol))

protected[tschuchort] def lowerTypeBoundTree[Lower](using q: Quotes)(using Type[Lower]) =
  import q.reflect.*
  TypeBoundsTree(TypeIdent(TypeRepr.of[Lower].typeSymbol), Inferred(TypeRepr.of[Any]))

protected[tschuchort] def upperTypeBoundTree[Upper](using q: Quotes)(using Type[Upper]) =
  import q.reflect.*
  TypeBoundsTree(Inferred(TypeRepr.of[Nothing]), TypeIdent(TypeRepr.of[Upper].typeSymbol))

protected[tschuchort] def refinementOf(using q: Quotes)(baseType: q.reflect.TypeRepr, fields: (String, q.reflect.TypeRepr)*) =
  import q.reflect.*
  fields.foldLeft(baseType) { case (prev, (fieldName, fieldType)) =>
    Refinement(prev, fieldName, fieldType)
  }

extension (using q: Quotes)(tpe: q.reflect.TypeRepr)
  /** Case class fields zipped with their global TypeRepr */
  protected[tschuchort] def caseFieldsWithTypes: List[(String, q.reflect.TypeRepr)] =
    import q.reflect.*
    tpe.typeSymbol.caseFields.map { symbol =>
      (symbol.name, tpe.memberType(symbol).typeSymbol.pipe(TypeIdent.apply).tpe)
    }

extension (using q: Quotes)(tpe: q.reflect.TypeRepr)
  /** TypeReprs of child classes */
  @targetName("TypeReprChildrenTypes")
  protected[tschuchort] def childrenTypes: List[q.reflect.TypeRepr] =
    import q.reflect.*
    tpe.typeSymbol.children.map { cs => TypeTree.ref(cs).tpe }

extension (using q: Quotes)(typeSymbol: q.reflect.Symbol)
  /** TypeReprs of child classes */
  @targetName("symbolChildrenTypes")
  protected[tschuchort] def childrenTypes: List[q.reflect.TypeRepr] =
    import q.reflect.*
    assert(typeSymbol.isType)
    typeSymbol.children.map { cs => TypeTree.ref(cs).tpe }

protected[tschuchort] def requireDynamicMethodName(using q: Quotes)(
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

protected[tschuchort] def parseDynamicArgsExpr(using q: Quotes)(
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
protected[tschuchort] def checkAndNormalizeParams(using q: Quotes)(
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

enum ShowTypeOptions:
  case ShortName, FqName, Widen, WidenByName, WidenTermRefByName, Simplified

object ShowTypeOptions:
  given FromExpr[ShowTypeOptions] with
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

protected[tschuchort] inline def showType[T](inline options: ShowTypeOptions*): String & scala.Singleton =
  ${ showTypeImpl[T]('options) }

inline def showType[T]: String & scala.Singleton =
  ${ showTypeImpl[T]('{ Seq(ShowTypeOptions.ShortName) }) }

private def showTypeImpl[T: Type](optionsExpr: Expr[Seq[ShowTypeOptions]])(using q: Quotes): Expr[String & scala.Singleton] =
  import q.reflect.{*, given}
  import ShowTypeOptions.{*, given}

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
