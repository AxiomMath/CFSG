module

public import Certificates.Kernel.Misc.KGroups.U33Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.GH74.KGroups.U33Inputs
public import Certificates.Data.Kernel.Misc.KGrp

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.U33K

open CFSG.KC.Ord CFSG.KC.Misc.KG CFSG.KC.LQT.P

noncomputable def uaGuard (n j v : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (nat_lit 0) v (Nat.blt j n)

noncomputable def uaCommT (n x y : Nat) : Bool :=
  allN n fun i => Nat.beq (img x (img y i)) (img y (img x i))

noncomputable def uaSqT (n c : Nat) : Bool := allN n fun i => Nat.beq (img c (img c i)) i

noncomputable def uaCubeT (n c : Nat) : Bool :=
  allN n fun i => Nat.beq (uaGuard n (img c i) (img c (img c (img c i)))) i

noncomputable def uaCubeP (n c : Nat) : Bool :=
  allN n fun i => letB (img c i) fun a => letB (img c a) fun b => letB (img c b) fun d =>
    Nat.beq (uaGuard n a (uaGuard n b (uaGuard n d d))) i

noncomputable def uaOrd2T (n c : Nat) : Bool := andB (notB (isOne n c)) (uaSqT n c)

noncomputable def uaOrd3T (n c : Nat) : Bool :=
  andB (notB (isOne n c)) (andB (notB (uaSqT n c)) (uaCubeT n c))

noncomputable def uaInC3T (n : Nat) (E : Nat → Nat) (r : Nat) (CL : List Nat) (k : Nat) : Bool :=
  letB (E k) fun g => impB (andB (uaCommT n g r) (uaCubeP n g)) (memL g CL)

noncomputable def uaCentT (n : Nat) (E : Nat → Nat) (a b k : Nat) : Bool :=
  letB (E k) fun s => impB (andB (uaCommT n s a) (uaCommT n s b)) (isOne n s)

theorem uaImgLt (s j : Nat) : img s j < 32 := by
  rw [img_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem uaImgOfFn {n : Nat} {g : Nat → Nat} (h : ∀ i < n, g i < 32) (j : Nat) :
    img (ofFn n g) j = uaGuard n j (g j) := by
  rw [img_eq, ofFn_eq, uaGuard]
  by_cases hj : j < n
  · rw [E_digit h hj, (blt_iff (a := j) (b := n)).2 hj]
  · have hb : Nat.blt j n = false := Bool.eq_false_iff.2 fun e => hj (blt_iff.1 e)
    have hl : E g n < 32 ^ j :=
      lt_of_lt_of_le (E_lt h) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt hl, hb]

theorem uaBeqOfFn {n : Nat} {f g : Nat → Nat} (hf : ∀ i < n, f i < 32) (hg : ∀ i < n, g i < 32) :
    Nat.beq (ofFn n f) (ofFn n g) = allN n fun i => Nat.beq (f i) (g i) := by
  refine Bool.eq_iff_iff.2 ?_
  rw [CFSG.KC.LQT.P.beq_iff, allN_iff, ofFn_eq, ofFn_eq]
  constructor
  · intro h i hi
    rw [CFSG.KC.LQT.P.beq_iff, ← E_digit hf hi, ← E_digit hg hi, h]
  · exact fun h => E_congr fun i hi => CFSG.KC.LQT.P.beq_iff.1 (h i hi)

theorem uaImgMul (n s t j : Nat) : img (mul n s t) j = uaGuard n j (img s (img t j)) :=
  uaImgOfFn (fun _ _ => uaImgLt _ _) j

theorem uaImgOne (n j : Nat) (hn : n ≤ 32) : img (one n) j = uaGuard n j j :=
  uaImgOfFn (fun _ hi => lt_of_lt_of_le hi hn) j

theorem uaComm_eq (n x y : Nat) : comm n x y = uaCommT n x y :=
  uaBeqOfFn (fun _ _ => uaImgLt _ _) (fun _ _ => uaImgLt _ _)

theorem uaIsOneMul (n a b : Nat) (hn : n ≤ 32) :
    isOne n (mul n a b) = allN n fun i => Nat.beq (img a (img b i)) i :=
  uaBeqOfFn (fun _ _ => uaImgLt _ _) (fun _ hi => lt_of_lt_of_le hi hn)

theorem uaOrdTwo (n c : Nat) (hn : n ≤ 32) : ordK n c 2 = uaOrd2T n c := by
  change letB c (fun a => andB (notB (isOne n a)) (isOne n (mul n a c))) = _
  rw [letB_eq, uaIsOneMul n c c hn]
  rfl

theorem uaOrdThree (n c : Nat) (hn : n ≤ 32) : ordK n c 3 = uaOrd3T n c := by
  change letB c (fun a => andB (notB (isOne n a)) (letB (mul n a c) fun b =>
    andB (notB (isOne n b)) (isOne n (mul n b c)))) = _
  rw [letB_eq, letB_eq, uaIsOneMul n c c hn, uaIsOneMul n (mul n c c) c hn]
  simp only [uaImgMul, uaOrd3T, uaSqT, uaCubeT]

theorem uaCube_eq (n c : Nat) (hn : n ≤ 32) : cubeOne n c = uaCubeP n c := by
  change isOne n (mul n (mul n (mul n (one n) c) c) c) = _
  rw [uaIsOneMul _ _ _ hn]
  simp only [uaImgMul, uaImgOne _ _ hn, uaCubeP, letB_eq]

theorem uaInC3_eq (n : Nat) (E : Nat → Nat) (r : Nat) (CL : List Nat) (hn : n ≤ 32) :
    inC3At n E r CL = uaInC3T n E r CL := by
  funext k
  rw [inC3At, uaInC3T, letB_eq, letB_eq, uaComm_eq, uaCube_eq _ _ hn]

theorem uaCent_eq (n : Nat) (E : Nat → Nat) (a b : Nat) : centAt n E a b = uaCentT n E a b := by
  funext k
  rw [centAt, uaCentT, letB_eq, letB_eq, uaComm_eq, uaComm_eq]

theorem uaH28 : (28 : Nat) ≤ 32 := by norm_num

end CertificateChecks.KernelMisc.U33K

public section

namespace CertificateChecks.KernelMisc.U33K

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG CFSG.KC.LQT.P
open CFSG.GH74.KGroups.U33

theorem treeA0 : allR 0 3024 (treeAt (mul 28) (one 28) AG 3 EA PAA) = true := by quickRfl
theorem treeA1 : allR 3024 3024 (treeAt (mul 28) (one 28) AG 3 EA PAA) = true := by quickRfl
theorem treeA2 : allR 6048 3024 (treeAt (mul 28) (one 28) AG 3 EA PAA) = true := by quickRfl
theorem treeA3 : allR 9072 3024 (treeAt (mul 28) (one 28) AG 3 EA PAA) = true := by quickRfl
theorem sortAB : allN 12096 (sortAt 12096 EA SGA) = true := by quickRfl
theorem closedA0 : allR 0 3024 (closedAt (mul 28) AG 3 12096 EA CTA) = true := by quickRfl
theorem closedA1 : allR 3024 3024 (closedAt (mul 28) AG 3 12096 EA CTA) = true := by quickRfl
theorem closedA2 : allR 6048 3024 (closedAt (mul 28) AG 3 12096 EA CTA) = true := by quickRfl
theorem closedA3 : allR 9072 3024 (closedAt (mul 28) AG 3 12096 EA CTA) = true := by quickRfl

theorem repB : andB (andB (inA (RG 0)) (ordK 28 (RG 0) 2)) (andB (andB (inA (RG 1))
    (ordK 28 (RG 1) 3)) (andB (inA (RG 2)) (ordK 28 (RG 2) 3))) = true := by quickRfl
theorem c2AB : Nat.beq (cntN 12096 fun k => ordK 28 (EA k) 2) 315 = true := by
  simp only [uaOrdTwo _ _ uaH28]
  quickRfl
theorem cAuB : Nat.beq (cntN 12096 fun k => comm 28 (EA k) (UG 0)) 192 = true := by
  simp only [uaComm_eq]
  quickRfl
theorem cAtB : Nat.beq (cntN 12096 fun k => comm 28 (EA k) (RG 0)) 48 = true := by
  simp only [uaComm_eq]
  quickRfl
theorem centAB : allN 12096 (centAt 28 EA (UG 0) (UG 1)) = true := by
  rw [uaCent_eq]
  quickRfl
theorem inuB : allN 12096 (inC3At 28 EA (UG 0) CLu) = true := by
  rw [uaInC3_eq _ _ _ _ uaH28]
  quickRfl
theorem intB : allN 12096 (inC3At 28 EA (RG 0) CLt) = true := by
  rw [uaInC3_eq _ _ _ _ uaH28]
  quickRfl
theorem e9uB : e9K 28 CLu = true := by quickRfl
theorem e9tB : e9K 28 CLt = true := by quickRfl
theorem c3AB : Nat.beq (cntN 12096 fun k => ordK 28 (EA k) 3) 728 = true := by
  simp only [uaOrdThree _ _ uaH28]
  quickRfl
theorem cA1B : Nat.beq (cntN 12096 fun k => comm 28 (EA k) (RG 1)) 216 = true := by
  simp only [uaComm_eq]
  quickRfl
theorem cA2B : Nat.beq (cntN 12096 fun k => comm 28 (EA k) (RG 2)) 18 = true := by
  simp only [uaComm_eq]
  quickRfl
theorem in1B : allN 12096 (inC3At 28 EA (RG 1) CL1) = true := by
  rw [uaInC3_eq _ _ _ _ uaH28]
  quickRfl
theorem in2B : allN 12096 (inC3At 28 EA (RG 2) CL2) = true := by
  rw [uaInC3_eq _ _ _ _ uaH28]
  quickRfl
theorem e27aB : e27K 28 (RG 1) CL1 = true := by quickRfl
theorem e27bB : e27K 28 (RG 2) CL2 = true := by quickRfl

theorem ordUVB : andB (ordK 28 (UG 0) 2) (andB (ordK 28 (UG 1) 7) (pairK 28 (UG 0) (UG 1) wsU)) =
    true := by quickRfl

end CertificateChecks.KernelMisc.U33K

end
