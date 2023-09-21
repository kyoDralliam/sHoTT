

```rzk
#lang rzk-1



#variables A B : U
#variables f g : A -> B
#variable θ : (x : A) → hom B (f x) (g x)
#variables x y : A
#variable u : hom A x y

#variable segal-B : is-segal B

#def covariant-pb (h : A → B) (C : B → U) (cov-C : is-covariant B C)
  : is-covariant A (\ z → C (h z))
  := \ a a' v c →
    cov-C (h a) (h a') (ap-hom A B h a a' v) c


#define naturality-lhs : hom B (f x) (g y) :=
  comp-is-segal B segal-B (f x) (g x) (g y) (θ x) (ap-hom A B g x y u)

#define naturality-rhs : hom B (f x) (g y) :=
  comp-is-segal B segal-B (f x) (f y) (g y) (ap-hom A B f x y u) (θ y)

#define naturality-inter-lhs : hom B (f x) (g y) :=
  comp-is-segal B segal-B (f x) (g x) (g y)
    (comp-is-segal B segal-B (f x) (f x) (g x) (id-hom B (f x)) (θ x))
    (ap-hom A B g x y u)

#define naturality-lhs-inter-eq : naturality-lhs = naturality-inter-lhs
  := postwhisker-homotopy-is-segal B segal-B (f x) (g x) (g y)
      (θ x)
      (comp-is-segal B segal-B (f x) (f x) (g x) (id-hom B (f x)) (θ x))
      (ap-hom A B g x y u)
      (rev (hom B (f x) (g x))
        (comp-is-segal B segal-B (f x) (f x) (g x) (id-hom B (f x)) (θ x))
        (θ x)
        (id-comp-is-segal B segal-B (f x) (g x) (θ x)))

#define naturality-inter-rhs : hom B (f x) (g y)
  :=
  comp-is-segal B segal-B (f x) (f y) (g y)
    (comp-is-segal B segal-B (f x) (f x) (f y) (id-hom B (f x)) (ap-hom A B f x y u))
    (θ y)

#define naturality-rhs-inter-eq : naturality-inter-rhs = naturality-rhs
  := postwhisker-homotopy-is-segal B segal-B (f x) (f y) (g y)
      (comp-is-segal B segal-B (f x) (f x) (f y) (id-hom B (f x)) (ap-hom A B f x y u))
      (ap-hom A B f x y u)
      (θ y)
      (id-comp-is-segal B segal-B (f x) (f y) (ap-hom A B f x y u))


#define ap-nat : dhom A x y u (\ z → hom B (f z) (g z)) (θ x) (θ y)
  := \ t → θ (u t)

#def covfbase uses (A) : is-covariant B (\ b → hom B (f x) b)
  := is-covariant-representable-is-segal B segal-B (f x)

#def covf uses (segal-B) : is-covariant A (\ a → hom B (f x) (f a))
   := covariant-pb f (\ b → hom B (f x) b) covfbase

#def covg uses (segal-B) : is-covariant A (\ a → hom B (f x) (g a))
   := covariant-pb g (\ b → hom B (f x) b) covfbase

#def φ (a : A) : hom B (f x) (f a) → hom B (f x) (g a)
  := \ v → comp-is-segal B segal-B (f x) (f a) (g a) v (θ a)

#def naturality-square-inter uses (θ) : naturality-inter-lhs = naturality-inter-rhs
  := naturality-covariant-fiberwise-transformation A x y u
       (\ a → hom B (f x) (f a))
       (\ a → hom B (f x) (g a))
       covf
       covg
       φ
       (id-hom B (f x))

#def naturality-square uses (θ) : naturality-lhs = naturality-rhs
  :=
  concat (hom B (f x) (g y))
    naturality-lhs
    naturality-inter-rhs
    naturality-rhs
    (concat (hom B (f x) (g y))
        naturality-lhs
        naturality-inter-lhs
        naturality-inter-rhs
        naturality-lhs-inter-eq
        naturality-square-inter)
    naturality-rhs-inter-eq
```
