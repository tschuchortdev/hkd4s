package com.tschuchort.hkd

import cats.{Applicative, Functor, Id}
import shapeless3.deriving.{K0, K11, summonAsArray}

import scala.compiletime.{constValue, summonInline}
import internal.{ArrayProduct, `*`, `.`}

import alleycats.Pure
import com.tschuchort.hkd
import com.tschuchort.hkd.FunctorK.{MapKGiven2Helper, MapKGiven3Helper, MapKGiven4Helper, MapKGivenHelper}

import scala.deriving.Mirror
import scala.util.chaining.*

trait InvariantK[D[_[_]]] {
  extension [F[_]](df: D[F]) def imapK[G[_]](fg: [A] => F[A] => G[A])(gf: [A] => G[A] => F[A]): D[G]
}

trait FunctorK[D[_[_]]] extends InvariantK[D] {
  extension [F[_]](df: D[F]) {
    def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G]

    override def imapK[G[_]](fg: [A] => F[A] => G[A])(gf: [A] => G[A] => F[A]): D[G] = mapK(fg)

    def mapKGiven[I[_]] = new MapKGivenHelper[I, D, F](df)(using this)
    def mapKGiven2[I1[_], I2[_]] = new MapKGiven2Helper[I1, I2, D, F](df)(using this)
    def mapKGiven3[I1[_], I2[_], I3[_]] = new MapKGiven3Helper[I1, I2, I3, D, F](df)(using this)
    def mapKGiven4[I1[_], I2[_], I3[_], I4[_]] = new MapKGiven4Helper[I1, I2, I3, I4, D, F](df)(using this)
  }
}

object FunctorK {
  inline def derived[D[_[_]]]: FunctorK[D] = apply
  inline def apply[D[_[_]]]: FunctorK[D] = summonInline

  given monoFunctorK[A]: FunctorK[[F[_]] =>> F[A]] with {
    extension [F[_]](df: F[A]) override def mapK[G[_]](fg: [B] => F[B] => G[B]): G[A] = fg(df)
  }

  given functionFunctorK[A, P]: FunctorK[[F[_]] =>> P => F[A]] with {
    extension [F[_]](df: P => F[A]) override def mapK[G[_]](fg: [B] => F[B] => G[B]): P => G[A] = { (p: P) => fg(df(p)) }
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

  given wrappedFunctorK[D[_[_]], H[_]](using fkd: FunctorK[D], functorH: Functor[H]): FunctorK[[F[_]] =>> H[D[F]]] with {
    extension [F[_]](hdf: H[D[F]])
      override def mapK[G[_]](fg: [A] => F[A] => G[A]): H[D[G]] =
        functorH.map(hdf) { (df: D[F]) => fkd.mapK(df)(fg) }
  }

  class MapKGivenHelper[I[_], D[_[_]], F[_]](df: D[F])(using FunctorK[D]) {
    def apply[G[_]](fg: [A] => F[A] => I[F[A]] ?=> G[A])(using instances: HkdFieldInstances[D, F, I]): D[G] =
      instances.zip(df).mapK[G](
        [A] => (fieldAndInstance: (F[A], I[F[A]])) => fg(fieldAndInstance._1)(using fieldAndInstance._2)
      )
  }

  class MapKGiven2Helper[I1[_], I2[_], D[_[_]], F[_]](df: D[F])(using FunctorK[D]) {
    def apply[G[_]](fg: [A] => F[A] => (I1[F[A]], I2[F[A]]) ?=> G[A])(using
        instances1: HkdFieldInstances[D, F, I1],
        instances2: HkdFieldInstances[D, F, I2]
    ): D[G] = instances2.zip(instances1.zip(df)).mapK[G](
      [A] => (x: ((F[A], I1[F[A]]), I2[F[A]])) => fg(x._1._1)(using x._1._2, x._2)
    )
  }

  class MapKGiven3Helper[I1[_], I2[_], I3[_], D[_[_]], F[_]](df: D[F])(using FunctorK[D]) {
    def apply[G[_]](fg: [A] => F[A] => (I1[F[A]], I2[F[A]], I3[F[A]]) ?=> G[A])(using
        instances1: HkdFieldInstances[D, F, I1],
        instances2: HkdFieldInstances[D, F, I2],
        instances3: HkdFieldInstances[D, F, I3]
    ): D[G] = instances3.zip(instances2.zip(instances1.zip(df))).mapK[G](
      [A] => (x: (((F[A], I1[F[A]]), I2[F[A]]), I3[F[A]])) => fg(x._1._1._1)(using x._1._1._2, x._1._2, x._2)
    )
  }

  class MapKGiven4Helper[I1[_], I2[_], I3[_], I4[_], D[_[_]], F[_]](df: D[F])(using FunctorK[D]) {
    def apply[G[_]](fg: [A] => F[A] => (I1[F[A]], I2[F[A]], I3[F[A]], I4[F[A]]) ?=> G[A])(using
        instances1: HkdFieldInstances[D, F, I1],
        instances2: HkdFieldInstances[D, F, I2],
        instances3: HkdFieldInstances[D, F, I3],
        instances4: HkdFieldInstances[D, F, I4]
    ): D[G] = instances4.zip(instances3.zip(instances2.zip(instances1.zip(df)))).mapK[G](
      [A] =>
        (x: ((((F[A], I1[F[A]]), I2[F[A]]), I3[F[A]]), I4[F[A]])) =>
          fg(x._1._1._1._1)(using x._1._1._1._2, x._1._1._2, x._1._2, x._2)
    )
  }
}

trait ContravariantK[D[_[_]]] extends InvariantK[D] {
  extension [F[_]](df: D[F])
    def contramapK[G[_]](gf: [A] => G[A] => F[A]): D[G]
    override def imapK[G[_]](fg: [A] => F[A] => G[A])(gf: [A] => G[A] => F[A]): D[G] = contramapK(gf)
}

object ContravariantK {
  inline def derived[D[_[_]]]: ContravariantK[D] = apply
  inline def apply[D[_[_]]]: ContravariantK[D] = summonInline

  given functionContravariantK[A, B]: ContravariantK[[F[_]] =>> F[A] => B] with {
    extension [F[_]](df: F[A] => B)
      override def contramapK[G[_]](gf: [C] => G[C] => F[C]): G[A] => B = { x => df(gf(x)) }
  }

  given phantomContravariantK[A]: ContravariantK[[_[_]] =>> A] with {
    extension [F[_]](df: A)
      override def contramapK[G[_]](gf: [B] => G[B] => F[B]): A = df
  }

  given adtContravariantK[D[_[_]]](using inst: => K11.Instances[ContravariantK, D]): ContravariantK[D] with {
    extension [F[_]](df: D[F])
      override def contramapK[G[_]](gf: [A] => G[A] => F[A]): D[G] =
        inst.map(df)(
          [t[_[_]]] =>
            (fieldContravariantK: ContravariantK[t], field: t[F]) =>
              fieldContravariantK.contramapK(field)[G](gf)
        )
  }

  given wrappedContravariantK[D[_[_]], H[_]](using
      contrad: ContravariantK[D],
      functorH: Functor[H]
  ): ContravariantK[[F[_]] =>> H[D[F]]] with {
    extension [F[_]](hdf: H[D[F]])
      override def contramapK[G[_]](gf: [A] => G[A] => F[A]): H[D[G]] =
        functorH.map(hdf) { (df: D[F]) => contrad.contramapK(df)[G](gf) }
  }
}

trait ApplyK[D[_[_]]] extends FunctorK[D]:
  extension [F[_]](df: D[F]) {
    def map2K[G[_], H[_]](dg: D[G])(h: [A] => (F[A], G[A]) => H[A]): D[H]

    /** Alias for [[map2K]] */
    def zipWithK[G[_], H[_]](dg: D[G])(h: [A] => (F[A], G[A]) => H[A]): D[H] = map2K(dg)(h)

    def zipK[G[_]](dg: D[G]): D[F * G] = map2K(dg)([A] => (fa: F[A], ga: G[A]) => (fa, ga))

    def zip2K[G[_], H[_]](dg: D[G], dh: D[H]): D[[A] =>> (F[A], G[A], H[A])] =
      zipK(dg).zipK(dh).mapK([A] => (x: ((F[A], G[A]), H[A])) => (x._1._1, x._1._2, x._2))

    def zip3K[G[_], H[_], I[_]](dg: D[G], dh: D[H], di: D[I]): D[[A] =>> (F[A], G[A], H[A], I[A])] =
      zip2K(dg, dh).zipK(di).mapK([A] => (x: ((F[A], G[A], H[A]), I[A])) => (x._1._1, x._1._2, x._1._3, x._2))

    def zip4K[G[_], H[_], I[_], J[_]](dg: D[G], dh: D[H], di: D[I], dj: D[J]): D[[A] =>> (F[A], G[A], H[A], I[A], J[A])] =
      zip3K(dg, dh, di).zipK(dj).mapK([A] => (x: ((F[A], G[A], H[A], I[A]), J[A])) => (x._1._1, x._1._2, x._1._3, x._1._4, x._2))

    def unzipK[G[_]](dfg: D[F * G]): (D[F], D[G]) =
      (
        mapK(dfg)([A] => (pair: (F[A], G[A])) => pair._1),
        mapK(dfg)([A] => (pair: (F[A], G[A])) => pair._2)
      )

    def unzip3K[G[_], H[_]](dfgh: D[[A] =>> (F[A], G[A], H[A])]): (D[F], D[G], D[H]) =
      (
        mapK(dfgh)([A] => (pair: (F[A], G[A], H[A])) => pair._1),
        mapK(dfgh)([A] => (pair: (F[A], G[A], H[A])) => pair._2),
        mapK(dfgh)([A] => (pair: (F[A], G[A], H[A])) => pair._3)
      )

    def unzip4K[G[_], H[_], I[_]](dfghi: D[[A] =>> (F[A], G[A], H[A], I[A])]): (D[F], D[G], D[H], D[I]) =
      (
        mapK(dfghi)([A] => (pair: (F[A], G[A], H[A], I[A])) => pair._1),
        mapK(dfghi)([A] => (pair: (F[A], G[A], H[A], I[A])) => pair._2),
        mapK(dfghi)([A] => (pair: (F[A], G[A], H[A], I[A])) => pair._3),
        mapK(dfghi)([A] => (pair: (F[A], G[A], H[A], I[A])) => pair._4)
      )
  }

object ApplyK {
  inline def derived[D[_[_]]]: ApplyK[D] = apply
  inline def apply[D[_[_]]]: ApplyK[D] = summonInline

  given monoApplyK[X](using functorK: FunctorK[[F[_]] =>> F[X]]): ApplyK[[F[_]] =>> F[X]] with {
    export functorK.*

    extension [F[_]](df: F[X])
      override def map2K[G[_], H[_]](dg: G[X])(h: [A] => (F[A], G[A]) => H[A]): H[X] = h(df, dg)
  }

  given productApplyK[D[_[_]]](using functorK: FunctorK[D], pInst: K11.ProductInstances[ApplyK, D]): ApplyK[D] with {
    export functorK.*

    extension [F[_]](df: D[F])
      override def map2K[G[_], H[_]](dg: D[G])(h: [A] => (F[A], G[A]) => H[A]): D[H] =
        pInst.map2(df, dg)(
          [t[_[_]]] =>
            (fieldApplyK: ApplyK[t], fieldF: t[F], fieldG: t[G]) => fieldApplyK.map2K(fieldF)(fieldG)(h)
        )
  }
}

trait PureK[D[_[_]]] {
  def pureK[F[_]](gen: [A] => () => F[A]): D[F]
}
object PureK {
  inline def derived[D[_[_]]]: PureK[D] = apply
  inline def apply[D[_[_]]]: PureK[D] = summonInline

  given monoPureK[X]: PureK[[F[_]] =>> F[X]] with {
    override def pureK[F[_]](gen: [A] => () => F[A]): F[X] = gen()
  }

  given functionPureK[X, P]: PureK[[F[_]] =>> P => F[X]] with {
    override def pureK[F[_]](gen: [A] => () => F[A]): P => F[X] = { (p: P) => gen() }
  }

  given productPureK[D[_[_]]](using pInst: K11.ProductInstances[PureK, D]): PureK[D] with {
    override def pureK[F[_]](gen: [A] => () => F[A]): D[F] =
      pInst.construct(
        [t[_[_]]] => (fieldPureK: PureK[t]) => fieldPureK.pureK(gen)
      )
  }

  given wrappedPureK[D[_[_]], H[_]](using pd: PureK[D], pureH: Pure[H]): PureK[[F[_]] =>> H[D[F]]] with {
    def pureK[F[_]](gen: [A] => () => F[A]): H[D[F]] = pureH.pure(pd.pureK(gen))
  }
}

trait ApplicativeK[D[_[_]]] extends ApplyK[D] with PureK[D]:
  extension [F[_]](df: D[F])
    override def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G] =
      df.map2K[[_] =>> Unit, G](pureK([_] => () => ()))([A] => (x: F[A], _: Unit) => fg(x))

object ApplicativeK {
  inline def derived[D[_[_]]]: ApplicativeK[D] = apply
  inline def apply[D[_[_]]]: ApplicativeK[D] = summonInline

  /*given monoApplicativeK[A]: ApplicativeK[[F[_]] =>> F[A]] with {
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
  }*/

  given applicativeKFromPureKAndApplyK[D[_[_]]](using p: PureK[D], a: ApplyK[D]): ApplicativeK[D] with {
    export p.*
    export a.{mapK as _, *}
  }
}

trait TraverseK[D[_[_]]] extends FunctorK[D] {
  extension [F[_]](df: D[F])
    def traverseK[G[+_], H[_]](f: [A] => F[A] => G[H[A]])(using Applicative[G]): G[D[H]]

  extension [F[+_], G[_]](dfg: D[F `.` G])
    def sequenceK(using Applicative[F]): F[D[G]] = dfg.traverseK([A] => (a: F[G[A]]) => a)

  extension [F[_]](df: D[F])
    override def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G] = df.traverseK[cats.Id, G](fg)
}

object TraverseK {
  inline def derived[D[_[_]]]: TraverseK[D] = apply
  inline def apply[D[_[_]]]: TraverseK[D] = summonInline

  given monoTraverseK[X]: TraverseK[[F[_]] =>> F[X]] with {
    extension [F[_]](df: F[X])
      override def traverseK[G[+_], H[_]](f: [A] => F[A] => G[H[A]])(using Applicative[G]): G[H[X]] = f(df)
  }

  given adtTraverseK[D[_[_]]](using pInst: K11.Instances[TraverseK, D]): TraverseK[D] with {
    extension [F[_]](df: D[F])
      override def traverseK[G[+_], H[_]](f: [A] => F[A] => G[H[A]])(using Applicative[G]): G[D[H]] =
        pInst.traverse(df)(
          ([A, B] => (ga: G[A], ab: A => B) => Applicative[G].map(ga)(ab)).asInstanceOf[shapeless3.deriving.MapF[G]]
        )(
          [A] => (a: A) => Applicative[G].pure(a)
        )(
          [A, B] => (gg: G[A => B], ga: G[A]) => Applicative[G].ap(gg)(ga)
        )(
          [t[_[_]]] => (fieldTraversableK: TraverseK[t], field: t[F]) => fieldTraversableK.traverseK(field)(f)
        )
  }

  given wrappedTraverseK[D[_[_]], J[_]](using
      traversableD: TraverseK[D],
      traversableJ: cats.Traverse[J]
  ): TraverseK[[F[_]] =>> J[D[F]]] with {
    extension [F[_]](jdf: J[D[F]])
      def traverseK[G[+_], H[_]](f: [A] => F[A] => G[H[A]])(using Applicative[G]): G[J[D[H]]] =
        traversableJ.traverse(jdf) { (df: D[F]) => traversableD.traverseK(df)(f) }
  }

}

/*
/** The categorical dual of TraversableK. */
trait DistributiveK[D[_[_]]] extends FunctorK[D]:
  extension [F[_]: Functor, G[_]](fdg: F[D[G]])
    /** Distributes the effect [[F]] over the fields of the higher-kinded data type [[D]]. In other words, it turns an
 * [[F]]-effectful way of creating a `D[G]` into a pure `D[F . G]` with the effect [[F]] now wrapped around every field.
 */
    def distributeK: D[F `.` G]

  extension [F[_]: Functor, G[_]](fdb: F[D[G]])
    def cotraverseK(ct: [A] => F[G[A]] => F[A]): D[F] = mapK(distributeK(fdb))(ct)

  extension [A](ad: A => D[Id])
    def decomposeK: D[[R] =>> A => R] = distributeK(ad)

  extension [A](df: D[[R] =>> A => R])
    def recomposeK: A => D[Id] = { (a: A) => mapK(df)[Id]([B] => (f: A => B) => f(a)) }

object DistributiveK {
  inline def derived[D[_[_]]]: DistributiveK[D] = apply
  inline def apply[D[_[_]]]: DistributiveK[D] = summonInline

  given monoDistributiveK[X](using functorK: FunctorK[[F[_]] =>> F[X]]): DistributiveK[[F[_]] =>> F[X]] with {
    export functorK.*
    extension [F[_]: Functor, G[_]](fdg: F[G[X]])
      def distributeK(): ([H[_]] =>> H[X])[F `.` G] = fdg
  }

  inline given adtDistributiveK[D[_[_]]](using
      m: Mirror.Product { type MirroredType[f[_]] = D[f] },
      inst: K11.ProductInstances[DistributiveK, D]
  ): DistributiveK[D] = new DistributiveK[D] {
    val fieldCount: Int = constValue[Tuple.Size[m.MirroredElemLabels]]

    extension [F[_]: Functor, G[_]](fdg: F[D[G]])
      override def distributeK(): D[F `.` G] = ??? // m.fromProduct( Seq.range(0, inst.))

    extension [F[_]](df: D[F])
      override def mapK[G[_]](fg: [A] => F[A] => G[A]): D[G] = ???
  }

}*/
