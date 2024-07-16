package com.tschuchort.hkd
package internal

import scala.quoted.*
import scala.annotation.MacroAnnotation
import scala.annotation.experimental

@experimental
protected[tschuchort] class InspectTree extends MacroAnnotation {
  override def transform(using q: Quotes)(tree: q.reflect.Definition): List[q.reflect.Definition] =
    import q.reflect.{*, given}
    // printTastyTypeRepr(tree.symbol.owner.info.memberType(tree.symbol))
    println("-----------------------------------------------------")
    println(Printer.TreeShortCode.show(tree))
    printTastyTree(tree)
    List(tree)

}

protected[tschuchort] transparent inline def inspectTree(inline expr: Any): Any = ${ inspectTreeImpl('expr) }

private def inspectTreeImpl(expr: Expr[Any])(using q: Quotes): Expr[Any] =
  import q.reflect.*
  printTastyTree(expr.asTerm)
  expr
