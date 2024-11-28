package com.tschuchort.hkd

import cats.{Applicative, Id, Show}
import cats.data.Const
import cats.data.Writer
import cats.effect.IO
import com.tschuchort.hkd.internal.`.`
import cats.syntax.all
import cats.effect.unsafe.implicits.global

class TypeclassesTest extends munit.FunSuite {
  sealed trait FooHK[F[_]]
  case class Foo1HK[F[_]](a: F[Int]) extends FooHK[F]
  sealed trait Foo2HK[F[_]] extends FooHK[F] { val b: F[Int] }
  case class Foo21HK[F[_]](b: F[Int], c1: F[Int]) extends Foo2HK[F]
  case class Foo22HK[F[_]](b: F[Int], c2: F[Int]) extends Foo2HK[F]

  test("FunctorK maps product") {
    val foo = Foo1HK[Option](Some(1))
    assertEquals(
      FunctorK[Foo1HK].mapK(foo)([A] => (a: Option[A]) => a.toList),
      Foo1HK(List(1))
    )
  }

  test("FunctorK maps sum") {
    val foo = Foo21HK[Option](b = Some(1), c1 = None)
    assertEquals(
      FunctorK[Foo2HK].mapK(foo)([A] => (a: Option[A]) => a.toList),
      Foo21HK(List(1), List())
    )
  }

  test("FunctorK maps nested sum") {
    val foo: FooHK[Option] = Foo21HK[Option](b = Some(1), c1 = None)
    assertEquals(
      FunctorK[FooHK].mapK(foo)([A] => (a: Option[A]) => a.toList),
      Foo21HK(List(1), List())
    )
  }

  test("FunctorK maps phantom typed") {
    case class BarHK[F[_]](a: Int)
    val bar = BarHK[Option](1)
    assertEquals(
      FunctorK[BarHK].mapK(bar)([A] => (a: Option[A]) => a.toList),
      BarHK[List](1)
    )
  }

  test("FunctorK maps product of functions") {
    case class BarHK[F[_]](f: Int => F[Int])
    val bar = BarHK[Option]((x: Int) => None)
    val mapped = FunctorK[BarHK].mapK(bar)([A] => (a: Option[A]) => a.toList)
    assertEquals(
      mapped.f(1),
      bar.f(1).toList
    )
  }

  test("FunctorK maps recursive ADT") {
    sealed trait BarHK[F[_]]
    case class BarHKLeaf[F[_]](a: F[Int]) extends BarHK[F]
    case class BarHKBranch[F[_]](b: F[Int], tree: BarHK[F]) extends BarHK[F]

    val bar = BarHKBranch[Option](Some(1), BarHKLeaf(Some(2)))
    val mapped = FunctorK[BarHK].mapK(bar)([A] => (a: Option[A]) => a.toList)
    assertEquals(mapped, BarHKBranch[List](List(1), BarHKLeaf(List(2))))
  }

  test("FunctorK maps recursive wrapped ADT") {
    case class BarHK[F[_]](a: F[Int], tree: Option[BarHK[F]])

    val bar = BarHK[Option](Some(1), Some(BarHK(Some(2), None)))
    val mapped = FunctorK[BarHK].mapK(bar)([A] => (a: Option[A]) => a.toList)
    assertEquals(mapped, BarHK[List](List(1), Some(BarHK(List(2), None))))
  }

  test("FunctorK maps product with givens") {
    val foo = Foo1HK[Option](Some(1))
    val mapped = FunctorK[Foo1HK].mapKGiven(foo)[Show]([T] =>
      (field: Option[T]) => (s: Show[Option[T]]) ?=> Const[String, T](Show[Option[T]].show(field)))

    assertEquals(mapped, Foo1HK(Const("Some(1)")))
  }

  test("FunctorK maps nested sum with givens") {
    val foo = Foo22HK[Option](Some(1), Some(2))
    val mapped = FunctorK[Foo22HK].mapKGiven(foo)[Show]([T] =>
      (field: Option[T]) => (s: Show[Option[T]]) ?=> Const[String, T](Show[Option[T]].show(field)))

    assertEquals(mapped, Foo22HK(Const("Some(1)"), Const("Some(2)")))
  }

  sealed trait ContraHK[F[_]]
  case class Contra1HK[F[_]](a: F[Int] => String) extends ContraHK[F]
  sealed trait Contra2HK[F[_]] extends ContraHK[F] { val b: F[Int] => String }
  case class Contra21HK[F[_]](b: F[Int] => String, c1: F[Int] => String) extends Contra2HK[F]
  case class Contra22HK[F[_]](b: F[Int] => String, c2: F[Int] => String) extends Contra2HK[F]

  test("ContravariantK maps product") {
    val contra = Contra1HK({ (x: List[Int]) => x.toString })
    val mapped = ContravariantK[Contra1HK].contramapK[List](contra)[Option]([A] => (x: Option[A]) => x.toList)
    assertEquals(mapped.a(Option(1)), contra.a(List(1)))
  }

  test("ContravariantK maps nested sum") {
    val contra = Contra21HK(b = { (x: List[Int]) => x.toString }, c1 = { (x: List[Int]) => x.toString })
    val mapped = ContravariantK[ContraHK].contramapK[List](contra)[Option]([A] => (x: Option[A]) => x.toList)
    mapped match
      case mapped: Contra21HK[Option] =>
        assertEquals(mapped.b(Option(1)), contra.b(List(1)))
        assertEquals(mapped.c1(Option(1)), contra.c1(List(1)))
      case _ => throw AssertionError(s"Expected Contra21HK, was: $mapped")
  }

  test("TraverseK sequences effects") {
    case class BarHK[F[_]](a: F[Int], b: F[Int], c: F[Int])
    var res = ""
    // Have to use IO here because Writer won't type-check for some reason
    val bar = BarHK[IO `.` Option](IO { res += "1"; Some(1) }, IO { res += "2"; Some(2) }, IO { res += "3"; Some(3) })
    val bar2 = TraverseK[BarHK].sequenceK(bar).unsafeRunSync()
    assertEquals(res, "123")
    assertEquals(bar2, BarHK[Option](Some(1), Some(2), Some(3)))
  }
}
