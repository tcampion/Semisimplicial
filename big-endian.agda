{-# OPTIONS --without-K #-}
-- Big-endian binary natural numbers in agda.
-- The type of natural numbers is called Simp, because of a canonical bijection between (binary) natural numbers
-- and the simplices of the standard ∞-dimensional simple.
-- The type of bineary natural numbers with leading zeros is called Face, because of a canonical biejction
-- between such data and face maps of standard simplices.
-- For both data types, we keep track of the number of bits and the number of 1's in the type signature.
-- This is because we are interested in thinking about face maps, and this data encodes the (co)domains of these maps.
-- Based off little-endian agda code by Anders Mortberg 
-- https://github.com/agda/cubical/blob/master/Cubical/Data/BinNat/BinNat.agda

-- Besides a few variants of the successor relation (we do not prove the relation is functional here),
-- This module also provides the relation isPB, which is relevant to the simplicial interpretation of
-- binary natural numbers.
module big-endian where
  open import Data.Nat

  -- A "simplex" is the same thing as a big-endian natural number.
  data Simp : ∀ (n : ℕ) →
              ∀ (d : ℕ) →
              Set
  -- A "face" is the same thing as a big-endian natural number, possibly with leading zeros.
  data Face : ∀ (n : ℕ) →
              ∀ (d : ℕ) →
              Set
  -- This mutually inductive definition is inspired by a definition of little-endian natural numbers
  -- which Anders Mortberg has implemented in Agda.
  -- A simplex is either empty, or it's a face capped by a leading 1.
  data Simp where
    emp : Simp zero zero
    1x : ∀ {n d : ℕ} → Face n d →
         Simp (suc n) (suc d)
  -- A face is either just (the inclusion of) a simplex, or it's a face capped with a leading 0.
  data Face where
    inc : ∀ {n d : ℕ} → Simp n d →
          Face n d
    0x : ∀ {n d : ℕ} → Face n d →
         Face (suc n) d

  -- These tell you if there is a carry when taking the successor of your simplex / face. 
  -- That is, they hold if and only if your simplex / face is all 1's.
  data ModCarryS : ∀ {n d : ℕ} → Simp n d → 
                   Set
  data ModCarryF : ∀ {n d : ℕ} → Face n d → 
                   Set
  data ModCarryS where
    empcarry : ModCarryS emp
    1carry : ∀ {n d : ℕ} → ∀ {F : Face n d} → ModCarryF F → 
             ModCarryS (1x F)
  data ModCarryF where
    inccarry : ∀ {n d : ℕ} → ∀ {S : Simp n d} → ModCarryS S → 
               ModCarryF (inc S)

  -- isModSuc F sF holds iff 
  -- F and sF have the same number n of bits AND sF is the successor of F MODULO 2^n
  -- (isModSuc might be redundant, Really just need it for the carry-over from 1111 to 0000.
  --  This could be done by hand; 
  -- possibly it would be annoying if you needed some simplex to be definitionally equal to 1111 to invoke it?)
  data isModSuc : ∀ {n d : ℕ} → Face n d →
                  ∀ {d' : ℕ} → Face n d' →
                  Set
  --Then isSucF F sF holds iff 
  --F,sF have the same number on of bits AND sF is the successor of F (in particular, 2^n - 1 has no "flat successor")
  --Apologies: "flat successor" is a weird name.
  data isSucF : ∀ {n d : ℕ} → Face n d →
                ∀ {d' : ℕ} → Face n (suc d') →
                Set
  --isSuc is a vanilla successor indicator:
  -- isSuc S sS holds iff suc(S) = sS (they may fail to have the same number of bits)
  data isSuc : ∀ {n d : ℕ} → Simp n d →
               ∀ {n' d' : ℕ} → Simp (suc n') (suc d') →
               Set
  data isModSuc where
    -- suc(0) = 0 mod 2^0
    msemp : isModSuc (inc emp) (inc emp)
    -- The mod-successor of 1111 is 0000.
    mscarry : ∀ {n d : ℕ} → ∀ {F : Face n d} → ∀ {d' : ℕ} → ∀ {msF : Face n d'} → isModSuc F msF →
                    ModCarryF F →
                    isModSuc (inc (1x F)) (0x msF)
    -- If F has a successor sF with the same number of bits, then suc(0F) = 0(sF) (with the same number of bits).
    ms0x : ∀ {n d : ℕ} → ∀ {F : Face (suc n) d} → ∀ {d' : ℕ} → ∀ {sF : Face (suc n) (suc d')} → isSucF F sF →
                isModSuc (0x F) (0x sF)
    -- If F has a successor sF with the same number of bits, then suc(1F) = 1(sF) (with the same number of bits).
    ms1x : ∀ {n d : ℕ} → ∀ {F : Face (suc n) d} → ∀ {d' : ℕ} → ∀ {sF : Face (suc n) (suc d')} → isSucF F sF →
                isModSuc (inc (1x F)) (inc (1x sF))
  data isSucF where
    -- Note that (inc emp) has no flat-successor.
    --- This says that the successor of 01111 is 10000 (with the same number of bits)
    sfcarry : ∀ {n d : ℕ} → ∀ {F : Face n d} → ∀ {d' : ℕ} → ∀ {msF : Face n d'} → isModSuc F msF →
                   ModCarryF F →
                   isSucF (0x F) (inc (1x msF))
    -- This says that if F has a successor sF with the same number of bits, 
    -- then suc(0F) = 0(sF) (with the same number of bits)
    sf0x : ∀ {n d : ℕ} → ∀ {F : Face (suc n) d} → ∀ {d' : ℕ} → ∀ {sF : Face (suc n) (suc d')} → isSucF F sF →
                isSucF (0x F) (0x sF)
    -- This says that if F has a successor sF with the same number of bits,
    -- then suc(1F) = 1(sF) (with the same number of bits)
    sf1x : ∀ {n d : ℕ} → ∀ {F : Face (suc n) d} → ∀ {d' : ℕ} → ∀ {sF : Face (suc n) (suc d')} → isSucF F sF →
                isSucF (inc (1x F)) (inc (1x sF))
  data isSuc where
    -- This says that if (inc S) has a successor (inc sS) with the same number of bits, then S has a successor sS
    fromsf : ∀ {n d : ℕ} → ∀ {S : Simp (suc n) d} → ∀ {d' : ℕ} → ∀ {sS : Simp (suc n) (suc d')} → isSucF (inc S) (inc sS) →
                  isSuc S sS
    -- This says that if (inc S) has a mod-successor msS, 
    -- and if a carry happened there (so that inc S = 1111 and msS = 0000), 
    -- then suc(S) = 1(msS)
    fromcarry : ∀ {n d : ℕ} → ∀ {S : Simp n d} → ∀ {d' : ℕ} → ∀ {msS : Face n d'} → isModSuc (inc S) msS →
                       ModCarryS S →
                       isSuc S (1x msS)

  -- isPB F G H holds if and only if 
  -- the G-face of the ideal represented by F is the ideal represented by H.
  -- In other words, if F is an ideal and G is a face, then the pullback H of F by G is 
  -- the ideal obtained by looking at the simplices in F which have 0's wherever G has 0's, 
  -- and then deleting those bits where G has 0's.
  --
  -- This is again an ideal because we are pulling back along the face map G, which
  -- is an order-preserving self-map of the natural numbers. 
  --
  -- G should have the same number of bits as F.
  -- The resulting H has as many bits as G has 1's.
  --
  -- It's natural for G to be of type Face, but F and H should really be of type Simp.
  -- However, the induction goes smoother if F and G are allowed to be faces.
  -- Moreover, later we will be using Face's to represent Simp's, using the "hack-y" fact
  -- that a Face with n bits is equivalent data to a Simp with =< n bits.
  --
  -- This pullback should be correct for either open or closed ideals, 
  -- except that for an open ideal the number of bits is a little wonky at the carry point:
  -- That is, the open ideal strictly below 1000 should be "pull-back-able" by a face map like
  -- 101 or something, since the open ideal is not actually using the extra point.
  -- In this setup, though, you'd have to pad and pullback by 0101 in this case.
  --
  -- This pullback operation is similar to the composition of face maps.
  -- In fact, composition of face maps may be defined as a relation in a similar style,
  -- and when you do this, the definition looks exactly the same except for the 4th constructor below, 10pb.
  -- It differs because F and H are representing ideals rather than faces.
  -- F and H generate bigger ideals than just themselves.
  data isPB : ∀ {n d : ℕ} → ∀ (F : Face n d) →
              ∀ {m : ℕ} → ∀ (G : Face n m) →
              ∀ {l : ℕ} → ∀ (H : Face m l) →
              Set where
    -- The pullback of the empty ideal by the empty face is the empty ideal.
    emppb : isPB (inc emp) (inc emp) (inc emp)
    -- If you add a leading 0 to F and to G, you get the same pullback as before.
    00pb : ∀ {n d : ℕ} → ∀ {F : Face n d} → ∀ {m : ℕ} → ∀ {G : Face n m} → ∀ {l : ℕ} → ∀ {H : Face m l} → isPB F G H →
                isPB (0x F) (0x G) H
    -- If you add a leading 0 to F and a leading 1 to G, you tack on a leading 0 to the pullback.
    01pb : ∀ {n d : ℕ} → ∀ {F : Face n d} → ∀ {m : ℕ} → ∀ {G : Face n m} → ∀ {l : ℕ} → ∀ {H : Face m l} → isPB F G H →
                isPB (0x F) (inc (1x G)) (0x H)
    -- If you add a leading 1 to F and a leading 0 to G, 
    -- your pullback will now be all 1's -- the same as pulling back G by itself. 
    -- NOT CLEAR THIS IS THE BEST WAY TO ENCODE THIS!
    10pb : ∀ {n d : ℕ} → ∀ (F : Face n d) → ∀ {m : ℕ} → ∀ {G : Face n m} → ∀ {H : Face m m} → isPB G G H →
                isPB (inc (1x F)) (0x G) H
    -- If you add a leading 1 to F and to G, your pullback will have a leading 1 tacked on.
    11pb : ∀ {n d : ℕ} → ∀ {F : Face n d} → ∀ {m : ℕ} → ∀ {G : Face n m} → ∀ {l : ℕ} → ∀ {H : Face m l} → isPB F G H →
               isPB (inc (1x F)) (inc (1x G)) (inc (1x H))


  --isPadOF F 00F holds if 00F is obtained from F by tacking on an arbitrary number of leading 0's.
  -- I worry that the use of this relation is going to cause headaches trying to write pattern-matching proofs later.
  data isPadOf : ∀ {n d : ℕ} → ∀ (F : Face n d) →
                 ∀ {n' : ℕ} → ∀ (00F : Face n' d) →
                 Set where
    -- F is obtained from itself by tacking on zero leading 0's.
    reflPad : ∀ {n d : ℕ} → ∀ (F : Face n d) →
              isPadOf F F
    -- If 00F is obtained from F by tacking on leading 0's, then so is 0(00F).
    sucPad : ∀ {n d : ℕ} → ∀ {F : Face n d} → ∀ {n' : ℕ} → ∀ {00F : Face n' d} → ∀ (pf : isPadOf F 00F) →
             isPadOf F (0x 00F)
    
  Delta+ : ∀ (n : ℕ) → Simp n n
  Delta+ zero = emp
  Delta+ (suc n) = 1x (inc (Delta+ n))

  EmpInc : ∀ (n : ℕ) → Face n zero
  EmpInc zero = inc emp
  EmpInc (suc n) = 0x (EmpInc n)

  Point : ∀ (n : ℕ) → Simp (suc n) (suc zero)
  Point n = 1x (EmpInc n)

  predN : ℕ → ℕ
  predN zero = zero
  predN (suc n) = n

  PreDelta+ : ∀ (n : ℕ) → Face n (predN n)
  PreDelta+ zero = inc emp
  PreDelta+ (suc zero) = 0x (inc emp)
  PreDelta+ (suc (suc n)) = inc (1x (PreDelta+(suc n)))

  PreDelta : ∀ (n : ℕ) → Face (suc n) n
  PreDelta zero = 0x (inc emp)
  PreDelta (suc n) = inc (1x (PreDelta n))
