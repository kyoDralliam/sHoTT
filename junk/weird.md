#lang rzk-1

-- some path algebra that we need here

-- path reversal
#def rev : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> y =_{A} x
  := \(A : U) -> \(x : A) -> \(y : A) -> \(p : x =_{A} y) 
  -> idJ(A, x, \z -> \(_ : x =_{A} z) -> z =_{A} x, refl_{x : A}, y, p)

-- path composition by induction on the second path
#def concat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \z -> \p -> \q -> idJ(A, y, \(w : A) -> \(_ : y =_{A} w) -> (x =_{A} w), p, z, q)

-- application of functions to paths
#def ap : (A : U) -> (B : U) -> (x : A) -> (y : A) -> (f : (x : A) -> B) -> (p : x =_{A} y) -> (f x =_{B} f y)
  := \A -> \B -> \x -> \y -> \f -> \p -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> (f x =_{B} f y'), refl_{f x : B}, y, p)

-- transport in a type family along a path in the base
#def transport : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (u : B x) -> B y
  := \A -> \B -> \x -> \y -> \p -> \u -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> B y', u, y, p)

-- for later use a higher transport
#def transport2 : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (q : x =_{A} y) 
  -> (H : p =_{x =_{A} y} q) -> (u : B x) -> (transport A B x y p u) =_{B y} (transport A B x y q u)
  := \A -> \B -> \x -> \y -> \p -> \q -> \H -> \u -> idJ(x =_{A} y, p, \q' -> \H' -> (transport A B x y p u) =_{B y} (transport A B x y q' u), refl_{transport A B x y p u : B y}, q, H)  

-- homotopies

#def homotopy : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) -> U
    := \A -> \B -> \f -> \g -> (a : A) -> (f a =_{B} g a)
    
#def homotopy-rev : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) 
    -> (_ : homotopy A B f g) -> homotopy A B g f
    := \A -> \B -> \f -> \g -> \H -> \a -> rev B (f a) (g a) (H a)

#def homotopy-composition : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) -> (h : (_ : A) -> B)
    -> (H : homotopy A B f g) -> (K : homotopy A B g h) -> homotopy A B f h
    := \A -> \B -> \f -> \g -> \h -> \H -> \K -> \a -> concat B (f a) (g a) (h a) (H a) (K a)

-- homotopies of dependent functions
#def dhomotopy : (A : U) -> (B : (a : A) -> U) -> (f : (a : A) -> B a) -> (g : (a : A) -> B a) -> U  
    := \A -> \B -> \f -> \g -> (a : A) -> (f a =_{B a} g a)

#def dhomotopy-rev : (A : U) -> (B : (a : A) -> U) -> (f : (a : A) -> B a) -> (g : (a : A) -> B a) 
    -> (_ : dhomotopy A B f g) -> dhomotopy A B g f
    := \A -> \B -> \f -> \g -> \H -> \a -> rev (B a) (f a) (g a) (H a)

-- we define this in the path composition order
#def dhomotopy-composition : (A : U) -> (B : (a : A) -> U) -> (f : (a : A) -> B a) -> (g : (a : A) -> B a) -> (h : (a : A) -> B a)
    -> (H : dhomotopy A B f g) -> (K : dhomotopy A B g h) -> dhomotopy A B f h
    := \A -> \B -> \f -> \g -> \h -> \H -> \K -> \a -> concat (B a) (f a) (g a) (h a) (H a) (K a)

-- for simplicity, we define these for non-dependent functions
-- for some reason this fails with dhomotopy used for non-dependent functions
#def homotopy-postwhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) 
    -> (H : homotopy A B f g) -> (h : (_ : B) -> C) -> homotopy A C (\(x : A) -> h (f x)) (\(x : A) -> h (g x))
    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> ap B C (f a) (g a) h (H a)

-- FAILURE
-- #def fails-homotopy-postwhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) 
--    -> (H : dhomotopy A B f g) -> (h : (_ : B) -> C) -> dhomotopy A C (\(x : A) -> h (f x)) (\(x : A) -> h (g x))
--    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> ap B C (f a) (g a) h (H a)

#def homotopy-prewhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : B) -> C) -> (g : (_ : B) -> C) 
    -> (H : homotopy B C f g) -> (h : (_ : A) -> B) -> homotopy A C (\(x : A) -> f (h x)) (\(x : A) -> g (h x))
    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> H (h a)

-- FAILURE
-- #def fails-homotopy-prewhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : B) -> C) -> (g : (_ : B) -> C) 
--    -> (H : dhomotopy B C f g) -> (h : (_ : A) -> B) -> dhomotopy A C (\(x : A) -> f (h x)) (\(x : A) -> g (h x))
--    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> H (h a)

#def isContr : (A : U) -> U
  := \(A : U) -> ∑ (x : A), (y : A) -> x =_{A} y

#def contraction-center : (A : U) -> (_ : isContr A) -> A
  := \(A : U) -> \Aiscontr -> (first Aiscontr)

#def contracting-htpy : (A : U) -> (Aiscontr : isContr A) -> (z : A) -> (contraction-center A Aiscontr) =_{A} z
  := \A -> \Aiscontr -> second Aiscontr

#def prod : (A : U) -> (B : U) -> U
  := \(A : U) -> \(B : U) -> ∑ (x : A), B

-- defined to illustrate the syntax for terms in sigma types
#def diagonal : (A : U) -> (_ : A) -> prod A A
  := \A -> \a -> (a , a)

#def hasSection : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \A -> \B -> \f -> ∑ (s : (_ : B) -> A), (b : B) -> (f (s b)) =_{B} b 

#def hasRetraction : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \A -> \B -> \f -> ∑ (r : (_ : B) -> A), (a : A) -> (r (f a)) =_{A} a 

-- incoherent equivalences   
#def hasInverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \(A : U) -> \(B : U) -> \(f : (_ : A) -> B) -> ∑ (g : (_ : B) -> A), (prod ((x : A) -> (g (f x)) =_{A} x)) ((y : B) -> (f (g y)) =_{B} y)
 
-- equivalences are bi-invertible maps
#def isEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \(A : U) -> \(B : U) -> \(f : (_ : A) -> B) -> prod (hasRetraction A B f) (hasSection A B f)

#def isEquiv-section : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : isEquiv A B f) -> (_ : B) -> A
    := \A -> \B -> \f -> \fisequiv -> (first (second fisequiv))

#def isEquiv-retraction : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : isEquiv A B f) -> (_ : B) -> A
    := \A -> \B -> \f -> \fisequiv -> (first (first fisequiv))

#def isEquiv-htpic-inverses : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fisequiv : isEquiv A B f) 
    -> homotopy B A (isEquiv-section A B f fisequiv) (isEquiv-retraction A B f fisequiv)
    := \A -> \B -> \f -> \fisequiv -> homotopy-composition B A (isEquiv-section A B f fisequiv) (\x -> (isEquiv-retraction A B f fisequiv) (f ((isEquiv-section A B f fisequiv) x))) (isEquiv-retraction A B f fisequiv) 
    (homotopy-rev B A (\x -> ((isEquiv-retraction A B f fisequiv) (f ((isEquiv-section A B f fisequiv) x)))) (isEquiv-section A B f fisequiv)
    (homotopy-prewhisker B A A(\x -> (isEquiv-retraction A B f fisequiv) (f x)) (\x -> x) (second (first fisequiv)) (isEquiv-section A B f fisequiv)))
    (homotopy-postwhisker B B A (\x -> f ((isEquiv-section A B f fisequiv) x)) (\x -> x) (second (second fisequiv)) (isEquiv-retraction A B f fisequiv))

#def hasInverse-isEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> isEquiv A B f
  := \A -> \B -> \f -> \fhasinverse -> ((first fhasinverse, first (second fhasinverse)), (first fhasinverse, second (second fhasinverse)))

#def isEquiv-hasInverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : isEquiv A B f) -> hasInverse A B f 
    := \A -> \B -> \f -> \fisequiv -> (first (second fisequiv), 
    (homotopy-composition A A (\x -> ((isEquiv-section A B f fisequiv) (f x))) (\x -> ((isEquiv-retraction A B f fisequiv) (f x))) (\x -> x)  (homotopy-prewhisker A B A (isEquiv-section A B f fisequiv) (isEquiv-retraction A B f fisequiv) (isEquiv-htpic-inverses A B f fisequiv) f) second (first fisequiv) , second (second  fisequiv)))

#def hasInverse-inverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : B) -> A
    := \A -> \B -> \f -> \fhasinverse -> first (fhasinverse)

#def weird-but-fine : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
    := \A -> \B -> \f 
        -> ∑ (fhasinverse : (hasInverse A B f)), (hasInverse-inverse A B f fhasinverse) =_{(_ : B) -> A} (hasInverse-inverse A B f fhasinverse)

-- FAILURE
#def weird-but-fails : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
     := \A -> \B -> \f 
        -> ∑ (fhasinverse : (hasInverse A B f)), (hasInverse-inverse A B f fhasinverse) =_{(_ : B) -> A} (first (fhasinverse))