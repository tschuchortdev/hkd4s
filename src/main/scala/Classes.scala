package com.tschuchort.hkd

import cats.{Applicative, Functor, Id}
import shapeless3.deriving.K11

import scala.compiletime.summonInline
import scala.util.NotGiven
import com.tschuchort.hkd.internal.{`*`, `.`}

trait InvariantK[D[_[_]]] {
  extension [F[_]](df: D[F]) def imapK[G[_]](fg: [A] => F[A] => G[A])(gf: [A] => G[A] => F[A]): D[G]
}

trait FunctorK[D[_[_]]] extends InvariantK[D] {
  extension [F[_]](df: D[F])
    def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G]
    override def imapK[G[_]](fg: [A] => F[A] => G[A])(gf: [A] => G[A] => F[A]): D[G] = mapK(fg)
}

object FunctorK {
  inline def derived[D[_[_]]]: FunctorK[D] = apply

  inline def apply[D[_[_]]]: FunctorK[D] = summonInline

  given monoFunctorK[A]: FunctorK[[F[_]] =>> F[A]] with {
    extension [F[_]](df: F[A]) override def mapK[G[_]](fg: [B] => F[B] => G[B]): G[A] = fg(df)
  }

  given phantomFunctorK[A]: FunctorK[[_[_]] =>> A] with {
    extension [F[_]](df: A) override def mapK[G[_]](fg: [B] => F[B] => G[B]): A = df
  }

  given adtFunctorK[D[_[_]]](using inst: => K11.Instances[FunctorK, D]): FunctorK[D] with {
    extension [F[_]](df: D[F])
      override def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G] =
        inst.map(df)(
          [t[_[_]]] => (fieldFunctorK: FunctorK[t], field: t[F]) => fieldFunctorK.mapK(field)(fg)
        )
  }

  /*given productFunctorK[D[_[_]]] (using pInst: => K11.ProductInstances[FunctorK, D]): FunctorK[D] with {
    lazy val pi = pInst

    extension[F[_]] (df: D[F])
      override def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G] =
        pi.map(df) {
          [t[_[_]]] => (fieldFunctorK: FunctorK[t], field: t[F]) =>
            fieldFunctorK.mapK(field)(fg)
        }
  }*/

  /*given coproductFunctorK[D[_[_]]] (using cInst: => K11.CoproductInstances[FunctorK, D]): FunctorK[D] with {
    extension[F[_]] (df: D[F])
      override def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G] =
        cInst.fold(df) {
          [t[f[_]] <: D[f]] => (caseFunctorK: FunctorK[t], _case: t[F]) =>
            caseFunctorK.mapK(_case)(fg)
        }
  }*/

  given wrappedFunctorK[D[_[_]], H[_]](using fkd: FunctorK[D], functorH: Functor[H]): FunctorK[[F[_]] =>> H[D[F]]] with {
    extension [F[_]](hdf: H[D[F]])
      override def mapK[G[_]](fg: [A] => F[A] => G[A]): H[D[G]] =
        functorH.map(hdf) { (df: D[F]) => fkd.mapK(df)(fg) }
  }
}

trait ContravariantK[D[_[_]]] extends InvariantK[D] {
  extension [F[_]](df: D[F])
    def contramapK[G[_]](gf: [A] => G[A] => F[A]): D[G]
    override def imapK[G[_]](fg: [A] => F[A] => G[A])(gf: [A] => G[A] => F[A]): D[G] = contramapK(gf)
}

trait ApplyK[D[_[_]]] extends FunctorK[D]:
  extension [F[_]](df: D[F])
    def map2K[G[_], H[_]](dg: D[G])(h: [A] => (F[A], G[A]) => H[A]): D[H]

    /** Alias for [[map2K]] */
    def zipWithK[G[_], H[_]](dg: D[G])(h: [A] => (F[A], G[A]) => H[A]): D[H] = map2K(dg)(h)

    def zipK[G[_]](dg: D[G]): D[F * G] = map2K(dg)([A] => (fa: F[A], ga: G[A]) => (fa, ga))

    def unzipK[G[_]](dfg: D[F * G]): (D[F], D[G]) =
      (
        mapK(dfg)([A] => (pair: (F[A], G[A])) => pair._1),
        mapK(dfg)([A] => (pair: (F[A], G[A])) => pair._2)
      )

object ApplyK {
  inline def apply[D[_[_]]]: ApplyK[D] = summonInline
}

trait PureK[D[_[_]]]:
  def pureK[F[_]](gen: [A] => () => F[A]): D[F]

object PureK {
  inline def apply[D[_[_]]]: PureK[D] = summonInline
}

trait ApplicativeK[D[_[_]]] extends ApplyK[D] with PureK[D]:
  extension [F[_]](df: D[F])
    override def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G] =
      df.map2K[[_] =>> Unit, G](pureK([_] => () => ()))([A] => (x: F[A], _: Unit) => fg(x))

object ApplicativeK {
  inline def apply[D[_[_]]]: ApplicativeK[D] = summonInline

  given monoApplicativeK[A]: ApplicativeK[[F[_]] =>> F[A]] with {
    // noinspection TypeParameterShadow
    override def pureK[F[_]](gen: [A] => () => F[A]): F[A] = gen()

    extension [F[_]](df: F[A])
      //
      // noinspection TypeParameterShadow
      override def map2K[G[_], H[_]](dg: G[A])(h: [A] => (F[A], G[A]) => H[A]): H[A] =
        h(df, dg)
  }

  given productApplicativeK[D[_[_]]](using pInst: K11.ProductInstances[ApplicativeK, D]): ApplicativeK[D] with {
    override def pureK[F[_]](gen: [A] => () => F[A]): D[F] =
      pInst.construct(
        [t[_[_]]] => (fieldApplicativeK: ApplicativeK[t]) => fieldApplicativeK.pureK(gen)
      )

    extension [F[_]](df: D[F])
      override def map2K[G[_], H[_]](dg: D[G])(h: [A] => (F[A], G[A]) => H[A]): D[H] =
        pInst.map2(df, dg)(
          [t[_[_]]] =>
            (fieldApplicativeK: ApplicativeK[t], fieldF: t[F], fieldG: t[G]) => fieldApplicativeK.map2K(fieldF)(fieldG)(h)
        )
  }

  given applicativeKFromPureKAndApplyK[D[_[_]]](using p: PureK[D], a: ApplyK[D]): ApplicativeK[D] with {
    export p.*
    export a.{mapK as _, *}
  }
}

trait TraversableK[D[_[_]]] extends FunctorK[D]:
  extension [F[_]](df: D[F]) def traverseK[G[+_], H[_]](f: [A] => F[A] => G[H[A]])(using Applicative[G]): G[D[H]]

  extension [F[+_], G[_]](dfg: D[F `.` G]) def sequenceK(using Applicative[F]): F[D[G]] = dfg.traverseK([A] => (a: F[G[A]]) => a)

  extension [F[_]](df: D[F]) override def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G] = df.traverseK[cats.Id, G](fg)

object TraversableK {
  inline def apply[D[_[_]]]: TraversableK[D] = summonInline

  given monoTraversableK[A]: TraversableK[[F[_]] =>> F[A]] with {
    extension [F[_]](df: F[A])
      //
      // noinspection TypeParameterShadow
      override def traverseK[G[+_], H[_]](f: [A] => F[A] => G[H[A]])(using Applicative[G]): G[H[A]] = f(df)
  }

  given productTraversableK[D[_[_]]](using pInst: K11.ProductInstances[TraversableK, D]): TraversableK[D] with {
    extension [F[_]](df: D[F])
      override def traverseK[G[+_], H[_]](f: [A] => F[A] => G[H[A]])(using Applicative[G]): G[D[H]] =
        pInst.traverse(df)(Applicative[G].map.asInstanceOf[shapeless3.deriving.MapF[G]])(
          Applicative[G].pure.asInstanceOf[shapeless3.deriving.Pure[G]])(
          Applicative[G].ap.asInstanceOf[shapeless3.deriving.Ap[G]])(
          [t[_[_]]] => (fieldTraversableK: TraversableK[t], field: t[F]) => fieldTraversableK.traverseK(field)(f)
        )
  }
}

/** The categorical dual of TraversableK. */
trait DistributiveK[D[_[_]]] extends FunctorK[D]:
  extension [F[_]: Functor, G[_]](fdg: F[D[G]])
    /** Distributes the effect [[F]] over the fields of the higher-kinded data type [[D]]. In other words, it turns an
      * [[F]]-effectful way of creating a `D[G]` into a pure `D[F . G]` with the effect [[F]] now wrapped around every field.
      */
    def distributeK(): D[F `.` G]

  /*extension [A] (ad: A => D[Id])
    def decomposeK: D[A => _] = ???

  extension [A] (da: D[A => _])
    def recomposeK: A => D[Id] = ???*/

object DistributiveK {
  inline def apply[D[_[_]]]: DistributiveK[D] = summonInline
}
