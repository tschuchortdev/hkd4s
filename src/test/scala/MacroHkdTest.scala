package com.tschuchort.hkd

import cats.Id
import shapeless3.deriving.{K0, K11}

import scala.compiletime.testing.{typeCheckErrors, typeChecks}
import scala.deriving.Mirror
import scala.annotation.experimental

@experimental
class MacroHkdTest extends munit.FunSuite {
  sealed trait Foo
  case class Foo1(a: Int) extends Foo
  sealed trait Foo2 extends Foo { val b: Int }
  case class Foo21(b: Int, c1: Int) extends Foo2
  case class Foo22(b: Int, c2: Int, d: Int) extends Foo2

  test("case class can be constructed") {
    val h = HkdFor[Foo1, Option](Some(1))
    assertEquals(h.a, Some(1))
  }

  test("case class can be constructed with mixed named and unnamed arguments") {
    val h = HkdFor[Foo22, Id](1, c2 = 2, d = 3)
    assertEquals(h.b, 1)
    assertEquals(h.c2, 2)
    assertEquals(h.d, 3)
  }

  test("case class can be constructed with out-of-order named arguments") {
    val h = HkdFor[Foo22, Id](c2 = 2, d = 3, b = 1)
    assertEquals(h.b, 1)
    assertEquals(h.c2, 2)
    assertEquals(h.d, 3)
  }

  test("constructor errors when argument missing") {
    val errors = typeCheckErrors("HkdFor[Foo21, Id](1)")
    assertEquals(errors.map(_.message), Seq("Missing argument for parameter 'c1'"))
  }

  test("constructor errors when too many arguments") {
    val errors = typeCheckErrors("HkdFor[Foo21, Id](1, 2, 3)")
    assertEquals(errors.map(_.message), Seq("Unexpected argument"))
  }

  test("constructor errors when wrong argument type") {
    val errors = typeCheckErrors("""HkdFor[Foo21, Id]("hello", 2)""")
    assertEquals(errors.map(_.message), Seq("Found:    java.lang.String\nRequired: cats.Id[scala.Int]"))
  }

  test("can assign case class to superclass sum type") {
    val h: HkdFor[Foo, Id] = HkdFor[Foo1, Id](1)
  }

  test("can copy case class with positional arguments") {
    val h = HkdFor[Foo21, Id](1, 2)
    assertEquals(h.copy(3, 4), HkdFor[Foo21, Id](3, 4))
  }

  test("can copy case class with named arguments out-of-order") {
    val h = HkdFor[Foo21, Id](1, 2)
    assertEquals(h.copy(c1 = 4, b = 3), HkdFor[Foo21, Id](3, 4))
  }

  test("can copy case class with mixed named and unnamed arguments") {
    val h = HkdFor[Foo21, Id](1, 2)
    assertEquals(h.copy(3, c1 = 4), HkdFor[Foo21, Id](3, 4))
  }

  test("can copy case class with default parameters") {
    val h = HkdFor[Foo21, Id](1, 2)
    assertEquals(clue(h.copy(c1 = 3)), HkdFor[Foo21, Id](1, 3))
  }

  test("can derive fully applied mirror for products") {
    summon[Mirror.ProductOf[HkdFor[Foo1, Option]]]
  }

  test("can derive K0.ProductGeneric") {
    summon[K0.ProductGeneric[HkdFor[Foo1, Option]]]
  }

  test("can derive partially applied mirror for products") {
    summon[Mirror.Product { type MirroredType[F[_]] = HkdFor[Foo1, F] }]
  }

  test("can derive K11.ProductGeneric") {
    summon[K11.ProductGeneric[HkdFor_[Foo1]]]
  }

  test("can derive fully applied mirror for sums") {
    summon[Mirror.SumOf[HkdFor[Foo2, Option]]]
  }

  test("can derive K0.CoproductGeneric") {
    summon[K0.CoproductGeneric[HkdFor[Foo2, Option]]]
  }

  test("can derive partially applied mirror for sums") {
    summon[Mirror.Sum { type MirroredType[F[_]] = HkdFor[Foo2, F] }]
  }

  test("can derive K11.CoproductGeneric") {
    summon[K11.CoproductGeneric[HkdFor_[Foo2]]]
  }

  test("renders toString correctly") {
    val h: HkdFor[Foo, Id] = HkdFor[Foo22, Id](1, c2 = 2, d = 3)
    assertEquals(h.toString, "HkdFor[Foo22, ?](1, 2, 3)")
  }

  test("compares non-equal for nominally unrelated types with same fields") {
    case class A(a: Int)
    case class B(a: Int)
    val ha = HkdFor[A, Id](1)
    val hb = HkdFor[B, Id](1)
    assert(!ha.canEqual(hb))
    assert(!hb.canEqual(ha))
    assert(ha != hb)
  }

  test("canEqual HkdFor with same erased T") {
    val h1: HkdFor[Foo, Id] = HkdFor[Foo1, Id](1)
    val h2: HkdFor[Foo, Id] = HkdFor[Foo1, Id](2)
    assert(h1.canEqual(h2))
    assert(h2.canEqual(h1))
  }

  test("not canEqual HkdFor with different erased T") {
    val h1: HkdFor[Foo, Id] = HkdFor[Foo1, Id](1)
    val h2: HkdFor[Foo, Id] = HkdFor[Foo21, Id](2, 3)
    assert(!h1.canEqual(h2))
    assert(!h2.canEqual(h1))
  }

  test("canEqual does not depend on F") {
    val h1: HkdFor[Foo, Id] = HkdFor[Foo1, Id](1)
    val h2: HkdFor[Foo, Option] = HkdFor[Foo1, Option](Some(2))
    assert(h1.canEqual(h2))
    assert(h2.canEqual(h1))
  }

  test("implements Product") {
    val h: HkdFor[Foo, Id] = HkdFor[Foo21, Id](0, 1)
    assertEquals(h.productArity, 2)
    assertEquals(h.productElement(0), 0)
    assertEquals(h.productElement(1), 1)
  }

  test("throws compile-time error when selecting unknown field") {
    val errors = typeCheckErrors(
      """
        val h = HkdFor[Foo21, Id](1, 2)
        h.b
        h.x
        """)
    assertEquals(errors.map(_.lineContent.stripLeading().stripTrailing()), Seq("h.x"))
  }

  test("throws compile-time error when calling unknown method") {
    val errors = typeCheckErrors(
      """
          val h = HkdFor[Foo21, Id](1, 2)
          h.b
          h.f(123)
          """)
    assertEquals(errors.map(_.lineContent.stripLeading().stripTrailing()), Seq("h.f(123)"))
  }

  test("has covariant subtype relationship with simple F") {
    val h: HkdFor[Foo1, Option] = HkdFor[Foo1, Some](Some(1))
  }

  test("no contravariant subtype relationship with simple F") {
    val errors = typeCheckErrors("""val h: HkdFor[Foo1, Some] = HkdFor[Foo1, Option](Some(1))""")
    assert(clue(errors.size) == 1)
    assert(clue(errors.head.message).contains("Could not prove"))
    assert(clue(errors.head.message).contains("no implicit values were found that match type Option[Int] <:< Some[Int]"))
  }

  test("has covariant subtype relationship with complex F") {
    case class Bar(a: Int, b: String)

    type F1[X] = X match
      case Int     => Int
      case String  => String
      case Boolean => Unit

    type F2[X] = X match
      case String  => String
      case Int     => Int
      case Boolean => Nothing

    val h1: HkdFor[Bar, F1] = HkdFor[Bar, F2](1, "hello")
    val h2: HkdFor[Bar, F2] = HkdFor[Bar, F1](1, "hello")
  }

  test("no subtype relationship with incompatible F") {
    case class Bar(a: Int, b: String)

    type F1[X] = X match
      case Int    => Int
      case String => String

    type F2[X] = X match
      case Int    => Unit
      case String => Unit

    val errors = typeCheckErrors("""val h2: HkdFor[Bar, F2] = HkdFor[Bar, F1](1, "hello")""")

    assert(errors.size == 1)
    assert(clue(errors.head.message).contains("Could not prove"))
    assert(clue(errors.head.message).contains("no implicit values were found that match type F1[Int] <:< F2[Int]"))
  }

  test("has subtype relationship with erased F") {
    val h: HkdFor[Foo1, [_] =>> Any] = HkdFor[Foo1, Some](Some(1))
  }

  test("has subtype relationship with erased T and erased F") {
    val h: HkdFor[Any, [_] =>> Any] = HkdFor[Foo1, Some](Some(1))
  }

  test("type tests sealed subtype") {
    val h: HkdFor[Foo, Id] = HkdFor[Foo1, Id](1)
    h match
      case h: HkdFor[Foo2, Id] => fail("matched Foo2", clues(h))
      case h: HkdFor[Foo1, Id] => ()
      case _                   => fail("matched fallback", clues(h))
  }

  test("type tests nested sealed subtype as supertype") {
    val h: HkdFor[Foo, Id] = HkdFor[Foo22, Id](1, 2, 3)
    h match
      case h: HkdFor[Foo1, Id]  => fail("matched Foo1", clues(h))
      case h: HkdFor[Foo21, Id] => fail("matched Foo21", clues(h))
      case h: HkdFor[Foo2, Id]  => ()
      case _                    => fail("matched fallback", clues(h))
  }

  test("type tests and doesn't match unrelated T") {
    case class Bar()
    val h: HkdFor[Foo, Id] = HkdFor[Foo1, Id](1)

    val errors = typeCheckErrors(
      """
        h match
            case h: HkdFor[Bar, Id]  => ()
      """)

    assert(errors.size == 1)
    assert(clue(errors.head.message).contains("case is unreachable"))
    assert(clue(errors.head.message).contains("Bar is not a subtype of Foo"))
  }

  test("type tests and doesn't match same T unrelated F") {
    val h = HkdFor[Foo1, Option](Some(1))
    val errors = typeCheckErrors(
      """
        h match
          case h: HkdFor[Foo1, List]   => ()
        """)

    assertEquals(errors.length, 1)
    assert(clue(errors.head.message).contains("no implicit values were found that match type Option[Int] <:< List[Int]"))
  }

  test("type tests T subtype with simple F supertype") {
    val h: HkdFor[Foo, Some] = HkdFor[Foo1, Some](Some(1))
    h match
      case h: HkdFor[Foo2, Option]  => fail("matched Foo2", clues(h))
      case h: HkdFor[Foo21, Option] => fail("matched Foo21", clues(h))
      case h: HkdFor[Foo1, Option]  => ()
      case _                        => fail("matched fallback", clues(h))
  }

  test("type tests T subtype with complex F supertype") {}

  /* WILDCARDS CAUSE A COMPILER CRASH

  test("type tests T wildcard with simple F super type") {
    val h: HkdFor[Foo, Some] = HkdFor[Foo1, Some](Some(1))
    h match
      case h: HkdFor[?, Option] => ()
      case _                    => fail("matched fallback", clues(h))
  }

  test("type tests and matches T wildcard with unrelated F") {
    val h: HkdFor[Foo, Some] = HkdFor[Foo1, Some](Some(1))
    h match
      case h: HkdFor[?, List] => ()
      case _                  => fail("matched fallback", clues(h))
  }

  test("type tests and doesn't match ADT bounded T wildcard with unrelated F") {
    val h: HkdFor[Foo, Some] = HkdFor[Foo1, Some](Some(1))
    h match
      case h: HkdFor[? <: Foo, List] => fail("matched unrelated F", clues(h))
      case _                         => ()
  }*/

  test("pattern match extracts fields without type test") {
    val h = HkdFor[Foo22, Option](Some(1), Some(2), Some(3))
    h match {
      case HkdFor(a, b, c) =>
        summon[a.type <:< Option[Int]]
        summon[b.type <:< Option[Int]]
        summon[c.type <:< Option[Int]]
        assertEquals((a, b, c), (Some(1), Some(2), Some(3)))
    }
  }

  test("pattern match extracts fields with type test complex F") {
    case class Bar(a: Int, b: String)

    type F1[X] = X match
      case Int     => Int
      case String  => String
      case Boolean => Unit

    val h = HkdFor[Bar, F1](1, "hello")
    h match {
      case HkdFor(a, b) =>
        summon[a.type <:< Int]
        summon[b.type <:< String]
        assertEquals((a, b), (1, "hello"))
    }
  }

  test("pattern match extracts fields with inferred F, no type test") {
    val h = HkdFor[Foo22, Option](Some(1), Some(2), Some(3))
    h match {
      case HkdFor_[Foo22](a, b, c) => {
        summon[a.type <:< Option[Int]]
        summon[b.type <:< Option[Int]]
        summon[c.type <:< Option[Int]]
        assertEquals((a, b, c), (Some(1), Some(2), Some(3)))
      }
    }
  }

  test("pattern match extracts fields with inferred F, type test for subtype") {
    val h: HkdFor[Foo, Option] = HkdFor[Foo22, Option](Some(1), Some(2), Some(3))
    h match {
      case h: HkdFor[Foo1, Option] => fail("matched Foo1", clues(h))
      case HkdFor_[Foo22](a, b, c) => {
        summon[a.type <:< Option[Int]]
        summon[b.type <:< Option[Int]]
        summon[c.type <:< Option[Int]]
        assertEquals((a, b, c), (Some(1), Some(2), Some(3)))
      }
    }
  }

  test("calls type tests in matchExhaustively") {
    val h: HkdFor[Foo, Id] = HkdFor[Foo1, Id](1)
    h matchExhaustively {
      case h: HkdFor[Foo2, Id] => fail("matched Foo2", clues(h))
      case h: HkdFor[Foo1, Id] => ()
      case _                   => fail("matched fallback", clues(h))
    }
  }

  // can only be checked manually by eye
  test("matchExhaustively warns when not exhaustive".ignore) {
    val h: HkdFor[Foo, Id] = HkdFor[Foo1, Id](1)
    h matchExhaustively {
      case _: HkdFor[Foo1, Id] => ()
      // no case for Foo2
    }
  }

  test("FunctorK maps product") {
    val h = HkdFor[Foo1, Option](Some(1))
    val mapped = FunctorK[HkdFor_[Foo1]].mapK(h)([A] => (a: Option[A]) => a.toList)
    assertEquals(mapped, HkdFor[Foo1, List](List(1)))
  }

  test("FunctorK maps sum") {
    val h: HkdFor[Foo2, Option] = HkdFor[Foo21, Option](Some(1), Some(2))
    val mapped = FunctorK[HkdFor_[Foo2]].mapK(h)([A] => (a: Option[A]) => a.toList)
    assertEquals(mapped, HkdFor[Foo21, List](List(1), List(2)))
  }

  test("FunctorK maps nested sum") {
    val h: HkdFor[Foo, Option] = HkdFor[Foo21, Option](Some(1), Some(2))
    val mapped = FunctorK[HkdFor_[Foo]].mapK(h)([A] => (a: Option[A]) => a.toList)
    assertEquals(mapped, HkdFor[Foo21, List](List(1), List(2)))
  }

  /* NOT IMPLEMENTED YET

  test("FunctorK maps recursive ADT") {
    sealed trait Bar
    case class BarLeaf(a: Int) extends Bar
    case class BarBranch(b: Int, tree: Bar) extends Bar

    val bar = HkdFor[BarBranch, Option](Some(1), HkdFor[BarLeaf, Option](Some(2)))
    val mapped = FunctorK[HkdFor_[Bar]].mapK(bar)([A] => (a: Option[A]) => a.toList)
    assertEquals(mapped, HkdFor[BarBranch, List](List(1), HkdFor[BarLeaf, List](List(2))))
  }*/
}
