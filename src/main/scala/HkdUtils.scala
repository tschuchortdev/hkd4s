package com.tschuchort.hkd

import cats.data.Const
import com.tschuchort.hkd.internal.{ArrayProduct, `*`, `.`}
import shapeless3.deriving.{K11, summonAsArray}

import scala.deriving.Mirror

/** Summon [[HkdFieldInstances]] to summon instances for every possible field of a higher-kinded data type [[D]]. */
trait HkdFieldInstances[D[_[_]], F[_], I[_]] {
  def zip[G[_]](df: D[G]): D[[A] =>> (G[A], I[F[A]])]

  def instancesFor[G[_]](d: D[G])(using FunctorK[D]): D[I `.` F] =
    zip[G](d).mapK[I `.` F]([A] => (fieldAndInstance: (G[A], I[F[A]])) => fieldAndInstance._2)
}
object HkdFieldInstances {
  class OfProduct[D[_[_]], F[_], I[_]](private val fieldInstances: D[I `.` F])(using
      m: Mirror.Product { type MirroredType[G[_]] = D[G]; type MirroredElemTypes[G[_]] <: Tuple }
  ) extends HkdFieldInstances[D, F, I] {
    override def zip[G[_]](df: D[G]): D[[A] =>> (G[A], I[F[A]])] = {
      val fieldsArr = Tuple.fromProduct(df.asInstanceOf[Product]).toArray
      val instancesArr = Tuple.fromProduct(fieldInstances.asInstanceOf[Product]).toArray
      m.fromProduct(ArrayProduct(fieldsArr.zip(instancesArr).asInstanceOf[Array[Any]])).asInstanceOf[D[G * (I `.` F)]]
    }
  }

  class OfSum[D[_[_]], F[_], I[_]](private val casesInstances: Array[HkdFieldInstances[D, F, I]])(using
      m: Mirror.Sum { type MirroredType[G[_]] = D[G]; type MirroredElemTypes[G[_]] <: Tuple }
  ) extends HkdFieldInstances[D, F, I] {
    override def zip[G[_]](df: D[G]): D[[A] =>> (G[A], I[F[A]])] = {
      casesInstances(m.ordinal(df.asInstanceOf[m.MirroredMonoType])).zip(df)
    }
  }

  inline given [D[_[_]], F[_], I[_]](using
      m: Mirror.Product { type MirroredType[G[_]] = D[G]; type MirroredElemTypes[G[_]] <: Tuple }
  ): HkdFieldInstances.OfProduct[D, F, I] =
    HkdFieldInstances.OfProduct(
      m.fromProduct(ArrayProduct(summonAsArray[m.MirroredElemTypes[I `.` F]])).asInstanceOf[D[I `.` F]]
    )

  inline given [D[_[_]], F[_], I[_]](using
      m: Mirror.Sum { type MirroredType[G[_]] = D[G]; type MirroredElemTypes[G[_]] <: Tuple }
  ): HkdFieldInstances.OfSum[D, F, I] =
    HkdFieldInstances.OfSum(
      summonAsArray[K11.LiftP[[C[_[_]]] =>> HkdFieldInstances[C, F, I], m.MirroredElemTypes]]
        .asInstanceOf[Array[HkdFieldInstances[D, F, I]]]
    )
}
