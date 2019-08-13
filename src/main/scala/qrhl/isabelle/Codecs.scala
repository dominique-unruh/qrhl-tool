package qrhl.isabelle

import info.hupel.isabelle.Codec

object Codecs {
  implicit def tuple4[A : Codec, B : Codec, C : Codec, D : Codec]: Codec[(A, B, C, D)] = Codec[(A, (B, C, D))].transform[(A, B, C, D)](
    { case (a, (b, c, d)) => (a, b, c, d)  },
    { case (a, b, c, d) => (a, (b, c, d)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType}"
  )

  implicit def tuple5[A : Codec, B : Codec, C : Codec, D : Codec, E : Codec]: Codec[(A, B, C, D, E)] = Codec[(A, (B, C, D, E))].transform[(A, B, C, D, E)](
    { case (a, (b, c, d, e)) => (a, b, c, d, e)  },
    { case (a, b, c, d, e) => (a, (b, c, d, e)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType} * (${Codec[E].mlType}"
  )

  implicit def tuple6[A : Codec, B : Codec, C : Codec, D : Codec, E : Codec, F : Codec]: Codec[(A, B, C, D, E, F)] = Codec[(A, (B, C, D, E, F))].transform[(A, B, C, D, E, F)](
    { case (a, (b, c, d, e, f)) => (a, b, c, d, e, f)  },
    { case (a, b, c, d, e, f) => (a, (b, c, d, e, f)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType} * (${Codec[E].mlType} * (${Codec[F].mlType}"
  )

  implicit def tuple7[A : Codec, B : Codec, C : Codec, D : Codec, E : Codec, F : Codec, G : Codec]: Codec[(A, B, C, D, E, F, G)] = Codec[(A, (B, C, D, E, F ,G))].transform[(A, B, C, D, E, F ,G)](
    { case (a, (b, c, d, e, f, g)) => (a, b, c, d, e, f, g)  },
    { case (a, b, c, d, e, f, g) => (a, (b, c, d, e, f, g)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType} * (${Codec[E].mlType} * (${Codec[F].mlType} * (${Codec[G].mlType}"
  )

  implicit def tuple8[A : Codec, B : Codec, C : Codec, D : Codec, E : Codec, F : Codec, G : Codec, H : Codec]: Codec[(A, B, C, D, E, F, G, H)] = Codec[(A, (B, C, D, E, F, G, H))].transform[(A, B, C, D, E, F, G, H)](
    { case (a, (b, c, d, e, f, g, h)) => (a, b, c, d, e, f, g, h)  },
    { case (a, b, c, d, e, f, g, h) => (a, (b, c, d, e, f, g, h)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType} * (${Codec[E].mlType} * (${Codec[F].mlType} * (${Codec[G].mlType} * (${Codec[H].mlType}"
  )

  implicit def tuple9[A : Codec, B : Codec, C : Codec, D : Codec, E : Codec, F : Codec, G : Codec, H : Codec, I : Codec]: Codec[(A, B, C, D, E, F, G, H, I)] = Codec[(A, (B, C, D, E, F, G, H, I))].transform[(A, B, C, D, E, F, G, H, I)](
    { case (a, (b, c, d, e, f, g, h, i)) => (a, b, c, d, e, f, g, h, i)  },
    { case (a, b, c, d, e, f, g, h, i) => (a, (b, c, d, e, f, g, h, i)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType} * (${Codec[E].mlType} * (${Codec[F].mlType} * (${Codec[G].mlType} * (${Codec[H].mlType} * (${Codec[I].mlType}"
  )

  implicit def tuple10[A : Codec, B : Codec, C : Codec, D : Codec, E : Codec, F : Codec, G : Codec, H : Codec, I : Codec, J : Codec]: Codec[(A, B, C, D, E, F, G, H, I, J)] = Codec[(A, (B, C, D, E, F, G, H, I, J))].transform[(A, B, C, D, E, F, G, H, I, J)](
    { case (a, (b, c, d, e, f, g, h, i, j)) => (a, b, c, d, e, f, g, h, i, j)  },
    { case (a, b, c, d, e, f, g, h, i, j) => (a, (b, c, d, e, f, g, h, i, j)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType} * (${Codec[E].mlType} * (${Codec[F].mlType} * (${Codec[G].mlType} * (${Codec[H].mlType} * (${Codec[I].mlType} * (${Codec[J].mlType}"
  )

  implicit def tuple11[A:Codec, B:Codec, C:Codec, D:Codec, E:Codec, F:Codec, G:Codec, H:Codec, I :Codec, J: Codec, K:Codec]:
  Codec[(A,B,C,D,E,F,G,H,I,J,K)] = Codec[(A,(B,C,D,E,F,G,H,I,J,K))].transform[(A,B,C,D,E,F,G,H,I,J,K)](
    { case (a, (b, c, d, e, f, g, h, i, j, k)) => (a, b, c, d, e, f, g, h, i, j, k)  },
    { case (a, b, c, d, e, f, g, h, i, j, k) => (a, (b, c, d, e, f, g, h, i, j, k)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType} * (${Codec[E].mlType} * (${Codec[F].mlType} * (${Codec[G].mlType} * (${Codec[H].mlType} * (${Codec[I].mlType} * (${Codec[J].mlType} * (${Codec[K].mlType})"
  )

  implicit def tuple12[A:Codec, B:Codec, C:Codec, D:Codec, E:Codec, F:Codec, G:Codec, H:Codec, I :Codec, J: Codec, K:Codec, L:Codec]:
  Codec[(A,B,C,D,E,F,G,H,I,J,K,L)] = Codec[(A,(B,C,D,E,F,G,H,I,J,K,L))].transform[(A,B,C,D,E,F,G,H,I,J,K,L)](
    { case (a, (b, c, d, e, f, g, h, i, j, k, l)) => (a, b, c, d, e, f, g, h, i, j, k, l)  },
    { case (a, b, c, d, e, f, g, h, i, j, k, l) => (a, (b, c, d, e, f, g, h, i, j, k, l)) },
    s"(${Codec[A].mlType}) * (${Codec[B].mlType}) * (${Codec[C].mlType}) * (${Codec[D].mlType} * (${Codec[E].mlType} * (${Codec[F].mlType} * (${Codec[G].mlType} * (${Codec[H].mlType} * (${Codec[I].mlType} * (${Codec[J].mlType} * (${Codec[K].mlType})"
  )
}
