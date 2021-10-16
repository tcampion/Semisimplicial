{-# OPTIONS --without-K #-}
module semisimplicial where
  open import Agda.Primitive
  open import Data.Nat
  open import big-endian

  -- N-truncated, augmented semisimplicial types.
  -- Universe polymorphism has not been added yet 
  -- (should be very easy, at the cost of even more bloat of type signatures).
  -- There is a canonical bijection between natural numbers (thought of in big-endian encoding) and
  -- simplices of Δ^∞. An *ideal* is a downward-closed set of simplices in this ordering.
  -- Each nontrivial ideal is principal, so the ideals are well-ordered by inclusion,
  -- or equivalently by looking at their last face (the generator of the ideal) and ordering as a natural number.
  -- Not every simplicial subset of a simplex is an ideal, but among the ideals are the simplices themselves
  -- (in binary, a simplex is 11...11), as well as the boundaries of simplices (11...10).
  -- The definition here defines an N-truncated, augmented semismplicial type X by starting with
  -- an N-1 -truncated, augmented semisimplicial type XUnd, and then inductively defining the set of maps
  -- into X from each ideal in turn, until we reach the boundary of the N-simplex. 
  -- Then we supply a set of fillers for these boundaries, i.e. the set of N-simplices.
  -- Along the way we keep track of face relationships to know how to glue to get from one ideal to the next.

  -- A truncated augmented simplicial set which has simplices of augmented dimension =< N
  data sSet : ∀ (N : ℕ) → Set₁
  -- Filling data for spheres of augmented dimension N required to promote from sSet N to sSet (suc N)
  record FillData {N : ℕ} (XUnd : sSet N) : Set₁
  
  -- Build by induction on dimension.
  data sSet where
    Aug : Set → sSet 0
    reedy : ∀ {N : ℕ} → ∀ (XUnd : sSet N) →
            ∀ (XFill : FillData XUnd) →
            sSet (suc N)
  
  -- Given X and F, tells you the set of ideals in X of the shape "weakly preceeding F"
  -- Note that "a face with N+1 digits" is a sneaky equivalent to "a simplex with at most N+1 digits"
  IdealIn : ∀ {N : ℕ} → ∀ (X : sSet N) →
            ∀ {d : ℕ} → ∀ (F : Face N d) →
            Set
  -- Given X G, x, x', tells you whether x' is the G-shaped face of x. 
  -- F' will be the pullback of F by G, but padded out with zeros to have N bits.
  -- (It is not explicitly enforced that F' is the pullback, but the constructors will be such
  -- that no "isFaceOf" relation ever gets built when that is not the case)
  isFaceOf : ∀ {N : ℕ} → ∀ (X : sSet N) →
             ∀ {d : ℕ} → {F : Face N d} → ∀ (x : IdealIn X F ) →
             ∀ {d' : ℕ} → ∀ {F' : Face N d'} → ∀ (x' : IdealIn X F') →
             ∀ {n' : ℕ} → ∀ (G : Face N n') →
             Set
  
  -- The filling data just needs to tell you how to fill spheres.
  record FillData {N} XUnd where
    constructor fillData
    field
      FillX : IdealIn XUnd (PreDelta+ N) →
                          Set

  -- The following type deals with wrapping issues.
  -- When building an N-truncated semisimplicial type X, we will need to know
  -- when one ideal x in X was constructed from another ideal y in X
  -- via particular constructors. But this constructor could have been applied at *any*
  -- earlier stage k, and so x and y will be wrapped N-k times in the passage from a
  -- k-truncated semisimplicial set to an N-truncated one. Thus we won't be able to
  -- directly look at the constructors used to form y from x.
  -- The type isBuildOf keeps track of this information for us as we wrap things to increasing depth.
  --
  -- Let sx be of shape one bigger than x, let y be the last face of x, 
  -- and let sy be of shape one bigger than y. 
  -- Then isBuildOf x sx y sy will tell you if sx was built from x by attaching sy at y.
  isBuildOf : ∀ {N : ℕ} → ∀ (X : sSet N) → 
              ∀ {d : ℕ} → ∀ {F : Face N d} → ∀ (x : IdealIn X F) → 
              ∀ {sd : ℕ} → ∀ {sF : Face N sd} → 
              -- ∀ (fsf : isSucF F sF) →
              ∀ (sx : IdealIn X sF) →
              ∀ {e : ℕ} → ∀ {G : Face N e} → ∀ (y : IdealIn X G) →
              ∀ {se : ℕ} → ∀ {sG : Face N se} → 
              -- ∀ (gsg : isSucF G sG) →
              ∀ (sy : IdealIn X sG) →
              Set
  
  --These things will be defined inductively, with special cases for N = 0.
  data IdealIn0 (X0 : Set) :
                ∀ {d : ℕ} → ∀ (F : Face zero d) →
                Set where
    taut0 : ∀ (x : X0) → IdealIn0 X0 (inc emp)

  data isFaceOf0 (X0 : Set) : 
                ∀ {d : ℕ} → ∀ {F : Face zero d} → IdealIn0 X0 F →
                ∀ {d' : ℕ} → ∀ {F' : Face zero d'} → IdealIn0 X0 F' →
                ∀ {n' : ℕ} → ∀ (G : Face zero n') →
                Set where
    refl0 : ∀ (x : X0) → isFaceOf0 X0 (taut0 x) (taut0 x) (inc emp)

  data isBuildOf0 (X0 : Set) :
              ∀ {d : ℕ} → ∀ {F : Face 0 d} → ∀ (x : IdealIn0 X0 F) → 
              ∀ {sd : ℕ} → ∀ {sF : Face 0 sd} → 
              -- ∀ (fsf : isSucF F sF) →
              ∀ (sx : IdealIn0 X0 sF) →
              ∀ {e : ℕ} → ∀ {G : Face 0 e} → ∀ (y : IdealIn0 X0 G) →
              ∀ {se : ℕ} → ∀ {sG : Face 0 se} → 
              -- ∀ (gsg : isSucF G sG) →
              ∀ (sy : IdealIn0 X0 sG) →
              Set where
                           
  -- In dimension N+1, the definitions will be more complicated.
  data IdealInN {N : ℕ} (XUnd : sSet N) (XFill : FillData XUnd) :
                ∀ {d : ℕ} → ∀ (F : Face (suc N) d) →
                Set
  data isFaceOfN {N : ℕ} (XUnd : sSet N) (XFill : FillData XUnd) :
                  ∀ {d : ℕ} → ∀ {F : Face (suc N) d} → IdealInN XUnd XFill F →
                  ∀ {d' : ℕ} → ∀ {F' : Face (suc N) d'} → IdealInN XUnd XFill F' →
                  ∀ {n' : ℕ} → ∀ (G : Face (suc N) n') →
                  Set

  data isBuildOfN {N : ℕ} (XUnd : sSet N) (XFill : FillData XUnd) : 
              ∀ {d : ℕ} → ∀ {F : Face (suc N) d} → ∀ (x : IdealInN XUnd XFill F) → 
              ∀ {sd : ℕ} → ∀ {sF : Face (suc N) sd} → 
              -- ∀ (fsf : isSucF F sF) →
              ∀ (sx : IdealInN XUnd XFill sF) →
              ∀ {e : ℕ} → ∀ {G : Face (suc N) e} → ∀ (y : IdealInN XUnd XFill G) →
              ∀ {se : ℕ} → ∀ {sG : Face (suc N) se} → 
              -- ∀ (gsg : isSucF G sG) →
              ∀ (sy : IdealInN XUnd XFill sG) →
              Set
                                
  --Inductive definitions of all of this data.
  IdealIn (Aug X0) = IdealIn0 X0
  IdealIn (reedy XUnd XFill) = IdealInN XUnd XFill
  
  isFaceOf (Aug X0) = isFaceOf0 X0
  isFaceOf (reedy XUnd XFill) = isFaceOfN XUnd XFill
    
  -- isBuildOf (reedy XUnd XFill) = isBuildOfN XUnd XFill
  isBuildOf (Aug X0) = isBuildOf0 X0
  isBuildOf (reedy XUnd XFill) = isBuildOfN XUnd XFill
                               
  data IdealInN {N} XUnd XFill where
    --Inherit ideals from the previous dimension. Need to tack on a leading zero.
    oldN : ∀ {d : ℕ} → ∀ {F : Face N d} → ∀ (x : IdealIn XUnd F) →
            IdealInN XUnd XFill (0x F)
    -- Promote the ideal given by filling a sphere from the previous dimension.
    fillN : ∀ {x : IdealIn XUnd (PreDelta+ N)} → ∀ (z : FillData.FillX XFill x) →
             IdealInN XUnd XFill (0x (inc (Delta+ N)))

    --Build a new closed ideal from an open ideal and some previously-constructed filling data.
    -- sF is required to be a simplex, so that it is a *new* thing to build and not already previously constructed.
    -- x is of shape "strictly below sF".
    -- y is the sF-face of x, i.e. the boundary of the next simplex to be added to complete to "weakly below sF".
    -- so y ought to be of shape "boundary of a simplex", but this is not enforced explicitly.
    -- sy is an ideal (so should be in fact a simplex) filling y.
    -- We obtain buildN z xy of shape "weakly below S" by gluing z onto x along y.
    buildN :  ∀ {d : ℕ} → ∀ {F : Face (suc N) d} → ∀ (x : IdealInN XUnd XFill F) → 
              ∀ {sd : ℕ} → ∀ {sF : Simp (suc N) (suc sd)} → ∀ (fsf : isSucF F (inc sF)) →
              ∀ {e : ℕ} → ∀ {G : Face (suc N) e} → ∀ {y : IdealInN XUnd XFill G} →  ∀ (xy : isFaceOfN XUnd XFill x y (inc sF)) →
              ∀ {se : ℕ} → ∀ {sG : Face (suc N) (suc se)} → ∀ (gsg : isSucF G sG) →
              ∀ (sy : IdealInN XUnd XFill sG) →
              ∀ (ysy : isBuildOfN XUnd XFill y sy y sy) → 
              IdealInN XUnd XFill (inc sF)
  
  data isFaceOfN {N} XUnd XFill where
    --Inherit face relations from the previous dimension. Need to tack on a leading zero.
    -- If x' is a G - face of x in the previous dimension, 
    -- then oldN x' is a 0x G - face of oldN x, and also a 1x G -face of oldN x.
    oldOld0N : ∀ {d : ℕ} → ∀ {F : Face N d} → ∀ {d' : ℕ} → ∀ {F' : Face N d'} → ∀ {n' : ℕ} → ∀ {G : Face N n'} → 
                          ∀ {x : IdealIn XUnd F} → ∀ {x' : IdealIn XUnd F'} → ∀ (xx' : isFaceOf XUnd x x' G) →
              isFaceOfN XUnd XFill (oldN x) (oldN x') (0x G)
    oldOld1N : ∀ {d : ℕ} → ∀ {F : Face N d} → ∀ {d' : ℕ} → ∀ {F' : Face N d'} → ∀ {n' : ℕ} → ∀ {G : Face N n'} → 
                          ∀ {x : IdealIn XUnd F} → ∀ {x' : IdealIn XUnd F'} → ∀ (xx' : isFaceOf XUnd x x' G) →
              isFaceOfN XUnd XFill (oldN x) (oldN x') (inc (1x G))

    -- When filling a top-dimensional sphere from the previous dimension, need to inherit faces from the boundary being filled.
    -- If x is an N-sphere filled by z, and x' is an old G-face of x,
    -- then oldN x' is a 0x G - face of fillN z, and also a 1x G - face of fillN z.
    oldFill0N : ∀ {x : IdealIn XUnd (PreDelta+ N)} → ∀ (z : FillData.FillX XFill x) →
               ∀ {d : ℕ} → ∀ {F : Face N d} → ∀ {x' : IdealIn XUnd F} → ∀ {n' : ℕ} → ∀ {G : Face N n'} → ∀ (xx' : isFaceOf XUnd x x' G) →
               isFaceOfN XUnd XFill (fillN z)  (oldN x') (0x G)
    oldFill1N : ∀ {x : IdealIn XUnd (PreDelta+ N)} → ∀ (z : FillData.FillX XFill x) →
               ∀ {d : ℕ} → ∀ {F : Face N d} → ∀ {x' : IdealIn XUnd F} → ∀ {n' : ℕ} → ∀ {G : Face N n'} → ∀ (xx' : isFaceOf XUnd x x' G) →
               isFaceOfN XUnd XFill (fillN z)  (oldN x') (inc (1x G))

    -- When filling a top-dimensional sphere from the previous dimension, need to put in a reflexivity face relation.
    -- There are actually two -- one for the face 111111 and one for the face 011111
    reflFill0N : ∀ {x : IdealIn XUnd (PreDelta+ N)} → ∀ (z : FillData.FillX XFill x) →
                isFaceOfN XUnd XFill (fillN z) (fillN z) (0x (inc (Delta+ N)))
    reflFill1N : ∀ {x : IdealIn XUnd (PreDelta+ N)} → ∀ (z : FillData.FillX XFill x) →
                isFaceOfN XUnd XFill (fillN z) (fillN z) (inc (1x (inc (Delta+ N))))

    -- When building a new ideal, need to inherit faces from the open ideal being filled.
    -- This function takes 21 arguments, 7 of them explicit. I believe it is the second-longest type signature in the file.
    -- sF is required to be a simplex, so that it is a *new* thing to build and not already previously constructed.
    -- x is of shape "strictly below sF".
    -- y is the sF-face of x, i.e. the boundary of the next simplex to be added to complete to "weakly below sF".
    -- so y ought to be of shape "boundary of a simplex", but this is not enforced explicitly.
    -- sy is an ideal (so should be in fact a simplex) filling y.
    -- x' is a face of x.
    -- conclude that, when you glue sy to x along y, you have x' as a face.
    oldBuildN : ∀ {d : ℕ} → ∀ {F : Face (suc N) d} → ∀ (x : IdealInN XUnd XFill F) → 
              ∀ {sd : ℕ} → ∀ {sF : Simp (suc N) (suc sd)} → ∀ (fsf : isSucF F (inc sF)) →
              ∀ {e : ℕ} → ∀ {G : Face (suc N) e} → ∀ {y : IdealInN XUnd XFill G} →  ∀ (xy : isFaceOfN XUnd XFill x y (inc sF)) →
              ∀ {se : ℕ} → ∀ {sG : Face (suc N) (suc se)} → ∀ (gsg : isSucF G sG) →
              ∀ (sy : IdealInN XUnd XFill sG) →
              ∀ (ysy : isBuildOfN XUnd XFill y sy y sy) → 
              ∀ {d' : ℕ} → ∀ {F' : Face (suc N) d'} →  ∀ {x' : IdealInN XUnd XFill F'} → 
                             ∀ {n' : ℕ} → ∀ {H : Face (suc N) n'} → ∀ (xx' : isFaceOfN XUnd XFill x x' H) →
              isFaceOfN XUnd XFill (buildN x fsf xy gsg sy ysy) x' H

    -- When building a new ideal, need to put in "mixed" faces, built from faces of the open ideal being filled and the filling data.
    -- This constructor takes 32 arguments, 13 of them explicit. I believe that's the longest in the file.
    -- sF is required to be a simplex, so that it is a *new* thing to build and not already previously constructed.
    -- x is of shape "strictly below sF".
    -- y is the sF-face of x, i.e. the boundary of the next simplex to be added to complete to "weakly below sF".
    -- so y ought to be of shape "boundary of a simplex", but this is not enforced explicitly.
    -- sy is an ideal (so should be in fact a simplex) filling y.
    -- x' is a face of x.
    -- conclude that when you glue sy to x along y, then sx' is a face.
    mixBuildN : ∀ {d : ℕ} → ∀ {F : Face (suc N) d} → ∀ (x : IdealInN XUnd XFill F) → 
              ∀ {sd : ℕ} → ∀ {sF : Simp (suc N) (suc sd)} → ∀ (fsf : isSucF F (inc sF)) →
              ∀ {e : ℕ} → ∀ {G : Face (suc N) e} → ∀ {y : IdealInN XUnd XFill G} →  ∀ (xy : isFaceOfN XUnd XFill x y (inc sF)) →
              ∀ {se : ℕ} → ∀ {sG : Face (suc N) (suc se)} → ∀ (gsg : isSucF G sG) →
              ∀ (sy : IdealInN XUnd XFill sG) →
              ∀ (ysy : isBuildOfN XUnd XFill y sy y sy) → 
              ∀ {d' : ℕ} → ∀ {F' : Face (suc N) d'} →  ∀ {x' : IdealInN XUnd XFill F'} → 
                             ∀ {n' : ℕ} → ∀ {H : Face (suc N) n'} → ∀ (xx' : isFaceOfN XUnd XFill x x' H) →
              ∀ {sd' : ℕ} → ∀ {sF' : Simp (suc N) (suc sd)} → ∀ (f'sf' : isSucF F' (inc sF')) →
              ∀ (x'y : isFaceOfN XUnd XFill x' y (inc sF')) →
              ∀ {sx' : IdealInN XUnd XFill (inc sF')} → ∀ (x'sx'ysy : isBuildOfN XUnd XFill x' sx' y sy) → 
              ∀ {n'' : ℕ} → ∀ {F'' : Face n' n''} → ∀ (shf'' : isPB (inc sF) H F'') →
              ∀ {00F'' : Face (suc N) n''} → ∀ (00f'' : isPadOf F'' 00F'') →
              isFaceOfN XUnd XFill (buildN x fsf xy gsg sy ysy) sx' 00F''

  data isBuildOfN {N} XUnd XFill where
    -- Carry forward the old build relations from XUnd.
    oldIsBuildN : ∀ {d : ℕ} → ∀ {F : Face N d} → ∀ (x : IdealIn XUnd F) → 
              ∀ {sd : ℕ} → ∀ {sF : Face N (suc sd)} → ∀ (fsf : isSucF F sF) →
              ∀ (sx : IdealIn XUnd sF) →
              ∀ {e : ℕ} → ∀ {G : Face N e} → ∀ (y : IdealIn XUnd G) →
              ∀ {se : ℕ} → ∀ {sG : Face N (suc se)} → ∀ (gsg : isSucF G sG) →
              ∀ (sy : IdealIn XUnd sG) →
              isBuildOf XUnd x sx y sy →
              isBuildOfN XUnd XFill (oldN x) (oldN sx) (oldN y) (oldN sy)
    -- When filling an N-boundary, we have a reflexive build relationship.
    fillIsBuildN : ∀ {x : IdealIn XUnd (PreDelta+ N)} → ∀ (z : FillData.FillX XFill x) →
                 isBuildOfN XUnd XFill (oldN x) (fillN z) (oldN x) (fillN z)
    -- When we build a new ideal, record it here.
    buildIsBuildN : ∀ {d : ℕ} → ∀ {F : Face (suc N) d} → ∀ (x : IdealInN XUnd XFill F) → 
              ∀ {sd : ℕ} → ∀ {sF : Simp (suc N) (suc sd)} → ∀ (fsf : isSucF F (inc sF)) →
              ∀ {e : ℕ} → ∀ {G : Face (suc N) e} → ∀ {y : IdealInN XUnd XFill G} →  ∀ (xy : isFaceOfN XUnd XFill x y (inc sF)) →
              ∀ {se : ℕ} → ∀ {sG : Face (suc N) (suc se)} → ∀ (gsg : isSucF G sG) →
              ∀ (sy : IdealInN XUnd XFill sG) →
              ∀ (ysy : isBuildOfN XUnd XFill y sy y sy) → 
              isBuildOfN XUnd XFill x (buildN x fsf xy gsg sy ysy) y sy
  
