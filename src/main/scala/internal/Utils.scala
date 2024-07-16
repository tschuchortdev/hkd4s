package com.tschuchort.hkd
package internal

import scala.util.chaining.*
import scala.util.boundary
import scala.annotation.targetName
import scala.collection.IndexedSeqView
import scala.collection.mutable
import scala.deriving.Mirror
import scala.quoted.*
import cats.implicits.*
import cats.Functor
import scala.annotation.tailrec

protected[tschuchort] class ArrayProduct(val elems: Array[Any]) extends Product:
  def canEqual(that: Any): Boolean = true
  def productElement(n: Int): Any = elems(n)
  def productArity: Int = elems.length
  override def productIterator: Iterator[Any] = elems.iterator

/** Records the types of all leafs (case classes, case objects, enum cases) of a deep ADT hierarchy that may contain multiple
  * levels of sealed traits.
  */
trait AdtHierarchyLeafs[T] { type MirroredLeafTypes <: Tuple }

object AdtHierarchyLeafs:
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

extension (b1: Boolean)
  protected[tschuchort] infix def implies(b2: Boolean): Boolean = !b1 || b2

extension [T](s: IndexedSeq[T])
  protected[tschuchort] def movingWindow(windowSize: Int): Seq[IndexedSeqView[T]] =
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
  protected[tschuchort] def allDistinctBy[B](f: A => B): Boolean = s.distinctBy(f).length == s.length

extension [A](aas: Seq[A])
  /** Matches the elements in [[aas]] with the elements in [[bs]] according to the key function. The order of [[aas]] will be
    * maintained, optionally appending an additional [[None]] element at the end of the list to contain all the elements in [[bs]]
    * that did not have a corresponding match in [[aas]]. Each sequence of [[B]] matches for an [[A]] is in the order that they
    * appeared in the [[bs]] list.
    */
  protected[tschuchort] def matchBy[B, K](bs: Seq[B])(byA: A => K)(byB: B => K): Seq[(Option[A], Seq[B])] =
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
  protected[tschuchort] def collectAllOrNone[B](pf: PartialFunction[A, B]): Option[CC[B]] =
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
