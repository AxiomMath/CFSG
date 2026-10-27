module

public import Certificates.Kernel.SporSch.Ru.C2248T
public import Certificates.Kernel.SporSch.Ru.C2248Z
public import Certificates.Kernel.SporSch.Ru.C2248J
public import Certificates.Kernel.SporSch.Ru.C2248G
public import Certificates.Kernel.SporSch.Ru.CNFacts
public import Certificates.Kernel.SporSch.Ru.SmallFacts
public import Certificates.Kernel.SporSch.Ru.R2257P
public import Certificates.Kernel.SporSch.Ru.Rows2
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
public meta import CFSG.Sporadic.Schreier.RuCheckSylow
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.RuCheckLocalBase
public import CFSG.Sporadic.Schreier.RuCheckOrbitsBase
public import CFSG.Sporadic.Schreier.RuRestrictBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuCt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.KC.BfsPin CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuB1K CertificateChecks.KernelSporSch.RuLines
  CertificateChecks.KernelSporSch.Rows2

theorem cNs0 : canonK 4060 12 (mask 12) (4060 * 12) Ns0 = true := by quickRfl
theorem cNs1 : canonK 4060 12 (mask 12) (4060 * 12) Ns1 = true := by quickRfl
theorem cNs0I : canonK 4060 12 (mask 12) (4060 * 12) Ns0I = true := by quickRfl
theorem cNs1I : canonK 4060 12 (mask 12) (4060 * 12) Ns1I = true := by quickRfl
theorem cRF : allN 7 (fun i => canonK 1920 11 (mask 11) (1920 * 11) (RF i)) = true := by quickRfl
theorem cKS : allN 10 (fun j => canonK 1920 11 (mask 11) (1920 * 11) (RuKS.S j)) = true := by
  quickRfl
theorem cL : allN 41 (fun j => canonK 1920 11 (mask 11) (1920 * 11) (RuT1920.L j)) = true := by
  quickRfl
theorem cLI0 : canonK 1920 11 (mask 11) (1920 * 11) (RuLI1920 0) = true := by quickRfl
theorem cLI1 : canonK 1920 11 (mask 11) (1920 * 11) (RuLI1920 1) = true := by quickRfl
theorem eLen1 : Nat.beq (lenNL (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.1) 7 = true := by quickRfl
theorem eLen2 : Nat.beq (lenNL (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.2) 7 = true := by quickRfl
theorem cK0 : Nat.beq (rcnt (RuKS.LR 0)) 512 = true := by quickRfl

theorem toArray_getD {l : List Nat} {i : Nat} (hi : i < l.length) : l.toArray[i]! = l.getD i 0 := by
  rw [getElem!_pos _ i (by simpa using hi), List.getElem_toArray, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem allLt_eq_allN {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) : allLt n f = allN n g :=
  bool_eq_of_iff ⟨fun hf => allN_of_forall fun i hi => (h i hi) ▸ allLt_iff.1 hf i hi,
    fun hg => allLt_iff.2 fun i hi => (h i hi).symm ▸ allN_spec hg i hi⟩

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem not_true_or (b : Bool) : (!true || b) = b := by cases b <;> rfl

theorem cEi {i : Nat} (hi : i < 7) : canonK 4060 12 (mask 12) (4060 * 12) (EA i) = true :=
  allN_spec cE i hi

theorem ebfs : ruEBFS = (((ebfsK Ns0 Ns1 Ns0I Ns1I Z).1.map (unpack 4060 12)).toArray,
    (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.1.toArray, (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.2.toArray) :=
  ebfsK_sound z_eq RuF.zCanon ns0_eq ns1_eq pNs0 pNs1

theorem len1 : (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.1.length = 7 := by
  rw [← lenNL_eq]
  exact Nat.eq_of_beq_eq_true eLen1

theorem len2 : (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.2.length = 7 := by
  rw [← lenNL_eq]
  exact Nat.eq_of_beq_eq_true eLen2

theorem par_eq {i : Nat} (hi : i < 7) :
    ruEPar[i]! = (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.1.getD i 0 := by
  rw [ruEPar_def, ebfs]
  exact toArray_getD (by rw [len1]; exact hi)

theorem gen_eq {i : Nat} (hi : i < 7) :
    ruEGen[i]! = (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.2.getD i 0 := by
  rw [ruEGen_def, ebfs]
  exact toArray_getD (by rw [len2]; exact hi)

theorem ngens_eq {g : Nat} (hg : g < 2) : ruNGensA[g]! = unpack 4060 12 (gen2 Ns0 Ns1 g) ∧
    invCand 4060 ruNGensA[g]! = unpack 4060 12 (gen2 Ns0I Ns1I g) ∧
    canonK 4060 12 (mask 12) (4060 * 12) (gen2 Ns0 Ns1 g) = true ∧
    canonK 4060 12 (mask 12) (4060 * 12) (gen2 Ns0I Ns1I g) = true := by
  rcases g with _ | _ | g
  · exact ⟨ns0_eq, (inv_of ns0_eq pNs0).1, cNs0, cNs0I⟩
  · exact ⟨ns1_eq, (inv_of ns1_eq pNs1).1, cNs1, cNs1I⟩
  · omega

theorem conj_eq {g j : Nat} (hg : g < 2) (hj : j < 7) :
    ruConjA ruNGensA[g]! ruEArr[j]! =
      unpack 4060 12 (CFSG.KS.SporSch.conjP (gen2 Ns0 Ns1 g) (gen2 Ns0I Ns1I g) (EA j)) := by
  obtain ⟨h1, h2, h3, h4⟩ := ngens_eq hg
  rw [ruConjA, h2, h1, e_eq hj, compA_unpack h3 (cEi hj), compA_unpack (canonK_pcomp h3 (cEi hj)) h4]
  rfl

theorem cConj {g j : Nat} (hg : g < 2) (hj : j < 7) : canonK 4060 12 (mask 12) (4060 * 12)
    (CFSG.KS.SporSch.conjP (gen2 Ns0 Ns1 g) (gen2 Ns0I Ns1I g) (EA j)) = true := by
  obtain ⟨-, -, h3, h4⟩ := ngens_eq hg
  exact canonK_pcomp (canonK_pcomp h3 (cEi hj)) h4

theorem ef_eq {i : Nat} (hi : i < 7) : ruEF i = unpack 1920 11 (RF i) := by
  rw [ruEF, RuF.f_eq, RuF.fpos_eq, e_eq hi]
  exact resK_sound RuCe.fLt' (cEi hi) (allN_spec rfOK i hi)

theorem eFacts : ruEArr.size = 7 ∧ ruEPar.size = 7 ∧ ruEGen.size = 7 ∧ ruEArr[0]! = ruZA ∧
      (∀ i < 7, isInvA 4060 ruEArr[i]! (invCand 4060 ruEArr[i]!) = true) ∧
      (∀ i, 1 ≤ i → i < 7 → ruEPar[i]! < i ∧ ruEGen[i]! < 2 ∧
        eqA 4060 ruEArr[i]! (ruConjA ruNGensA[ruEGen[i]!]! ruEArr[ruEPar[i]!]!) = true) ∧
      (∀ i < 7, ∀ g < 2, ∃ j < 7, eqA 4060 (ruConjA ruNGensA[g]! ruEArr[i]!) ruEArr[j]! = true) ∧
      (∀ i < 7, ∀ j < 7, i ≠ j → eqA 4060 ruEArr[i]! ruEArr[j]! = false) ∧
      (∀ i < 7, eqA 4060 ruEArr[i]! (idA 4060) = false) ∧
      (∀ i < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[i]!) (idA 4060) = true) ∧
      (∀ i < 7, ∀ j < 7, i ≠ j →
        ∃ k < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[j]!) ruEArr[k]! = true) ∧
      (∀ i < 7, ∀ j < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[j]!)
        (compA 4060 ruEArr[j]! ruEArr[i]!) = true) ∧
      (∀ i < 7, ruSift 4060 (ruField4060 1) ruCBase ruEArr[i]! = true) ∧
      (∀ i < 7, siftA 1920 ruKLevels (ruBaseArr 1920 ruKBase) 0 (ruEF i) = true) ∧
      (∀ i < 7, ∀ k < 8, eqA 4060 (compA 4060 ruEArr[i]! ruKGensA[k]!)
        (compA 4060 ruKGensA[k]! ruEArr[i]!) = true) := by
  refine ⟨e_size, ?_, ?_, ?_, fun i hi => ?_, fun i h1 hi => ?_, fun i hi g hg => ?_,
    fun i hi j hj hij => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi j hj hij => ?_,
    fun i hi j hj => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi k hk => ?_⟩
  · rw [ruEPar_def, ebfs]
    simp [len1]
  · rw [ruEGen_def, ebfs]
    simp [len2]
  · rw [e_eq (by omega), z_eq, Nat.eq_of_beq_eq_true e0]
  · obtain ⟨h1, h2⟩ := invEqK_sound (allN_spec eInv i hi)
    rw [e_eq hi, h1]
    exact h2
  · have h := allN_spec eTree i hi
    rw [beq_false_of_ne (by omega : i ≠ 0), Bool.false_or, sb_eq, sb_eq] at h
    obtain ⟨hp, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hg, h⟩ := (bAnd_iff _ _).1 h
    have hp' : (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.1.getD i 0 < i := lt_of_blt hp
    have hg' : (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.2.getD i 0 < 2 := lt_of_blt hg
    rw [par_eq hi, gen_eq hi]
    refine ⟨hp', hg', ?_⟩
    rw [e_eq hi, conj_eq hg' (by omega), eqA_canon (cEi hi) (cConj hg' (by omega)), h]
  · obtain ⟨j, hj, h⟩ := anyK_spec (allN_spec (allN_spec eConj i hi) g hg)
    refine ⟨j, hj, ?_⟩
    rw [conj_eq hg hi, e_eq hj, eqA_canon (cConj hg hi) (cEi hj), h]
  · have h := allN_spec (allN_spec eDist i hi) j hj
    rw [beq_false_of_ne hij, Bool.false_or] at h
    rw [e_eq hi, e_eq hj, eqA_canon (cEi hi) (cEi hj)]
    cases e : Nat.beq (EA i) (EA j)
    · rfl
    · rw [e] at h
      exact absurd h Bool.false_ne_true
  · have h := allN_spec eNe i hi
    rw [e_eq hi, RuB1K.idA_eq, eqA_canon (cEi hi) RuB1K.cId]
    cases e : Nat.beq (EA i) (pidn 4060 12)
    · rfl
    · rw [e] at h
      exact absurd h Bool.false_ne_true
  · rw [e_eq hi, compA_unpack (cEi hi) (cEi hi), RuB1K.idA_eq,
      eqA_canon (canonK_pcomp (cEi hi) (cEi hi)) RuB1K.cId]
    exact allN_spec eSq i hi
  · have h := allN_spec (allN_spec eProd i hi) j hj
    rw [beq_false_of_ne hij, Bool.false_or] at h
    obtain ⟨k, hk, h⟩ := anyK_spec h
    refine ⟨k, hk, ?_⟩
    rw [e_eq hi, e_eq hj, e_eq hk, compA_unpack (cEi hi) (cEi hj),
      eqA_canon (canonK_pcomp (cEi hi) (cEi hj)) (cEi hk)]
    exact h
  · rw [e_eq hi, e_eq hj, compA_unpack (cEi hi) (cEi hj), compA_unpack (cEi hj) (cEi hi),
      eqA_canon (canonK_pcomp (cEi hi) (cEi hj)) (canonK_pcomp (cEi hj) (cEi hi))]
    exact allN_spec (allN_spec eComm i hi) j hj
  · obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 (allN_spec eSiftC i hi)
    exact siftK_sound RuCNF.bindsC RuCNF.pC RuCS.hl (e_eq hi) (range_of_canonK (cEi hi)) h2
  · obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 (allN_spec rfSiftK i hi)
    exact siftK_sound RuSF.bindsK RuSF.pK RuKS.hl (ef_eq hi)
      (range_of_permOK (allN_spec rfPerm i hi)) h2
  · have hk' := (RuCe.kok_spec hk).2
    rw [e_eq hi, RuCe.kg_eq hk, compA_unpack (cEi hi) hk', compA_unpack hk' (cEi hi),
      eqA_canon (canonK_pcomp (cEi hi) hk') (canonK_pcomp hk' (cEi hi))]
    exact allN_spec (allN_spec eKcomm i hi) k hk

theorem cLj {j : Nat} (hj : j < 41) : canonK 1920 11 (mask 11) (1920 * 11) (RuT1920.L j) = true :=
  allN_spec cL j hj

theorem cRFi {i : Nat} (hi : i < 7) : canonK 1920 11 (mask 11) (1920 * 11) (RF i) = true :=
  allN_spec cRF i hi

theorem eqA1920 {p q : Nat} (hp : canonK 1920 11 (mask 11) (1920 * 11) p = true)
    (hq : canonK 1920 11 (mask 11) (1920 * 11) q = true) :
    eqA 1920 (unpack 1920 11 p) (unpack 1920 11 q) = Nat.beq p q := eqA_unpack hp hq

theorem comm_eq {G X : Nat} (hG : canonK 1920 11 (mask 11) (1920 * 11) G = true)
    (hX : canonK 1920 11 (mask 11) (1920 * 11) X = true) :
    ruComm1920 (unpack 1920 11 G) (unpack 1920 11 X) = cm G X := by
  rw [ruComm1920, compA_unpack hG hX, compA_unpack hX hG,
    eqA1920 (canonK_pcomp hG hX) (canonK_pcomp hX hG)]
  rfl

theorem kf_eq {k : Nat} (hk : k < 10) : ruKF k = unpack 1920 11 (RuT1920.L (14 + k)) :=
  RuCe.f1920 14 10 (14 + k) rfl hk rfl (by omega)

theorem jf_eq {j : Nat} (hj : j < 10) : ruJF j = unpack 1920 11 (RuT1920.L (24 + j)) :=
  RuCe.f1920 24 10 (24 + j) rfl hj rfl (by omega)

theorem rowsK {f : Nat → Bool} (h : ∀ a < 512, f a = true) : ∀ a < rcnt (RuKS.LR 0), f a = true :=
  fun a ha => h a (by
    have := Nat.eq_of_beq_eq_true cK0
    omega)

theorem zkFacts : all2 1920 ruKLevels (fun g => !(allLt 8 fun k => ruComm1920 g (ruKF k)) ||
    eqA 1920 g (idA 1920) || (Nat.any 7 fun i _ => eqA 1920 g (ruEF i))) = true := by
  refine all2_of_rows_imp RuSF.bindsK RuSF.pK RuKS.hl (Nat.le_refl 2) (fun G hG h => ?_)
    (rowsK ZK.all)
  have hA : (allLt 8 fun k => ruComm1920 (unpack 1920 11 G) (ruKF k)) =
      allN 8 (fun k => cm G (RuT1920.L (Nat.add 14 k))) :=
    allLt_eq_allN fun k hk => by
      rw [kf_eq (by omega)]
      exact comm_eq hG (cLj (by omega))
  unfold zkpK at h
  rw [hA]
  cases hc : allN 8 (fun k => cm G (RuT1920.L (Nat.add 14 k)))
  · rfl
  · rw [hc] at h
    have h' : bIf(Nat.beq G (pidn 1920 11), true, anyK 7 (fun i => Nat.beq G (RF i))) = true := h
    rw [not_true_or, RuP.idA_eq, eqA1920 hG RuP.cId]
    cases e : Nat.beq G (pidn 1920 11)
    · rw [e] at h'
      have h'' : anyK 7 (fun i => Nat.beq G (RF i)) = true := h'
      obtain ⟨i, hi, hb⟩ := anyK_spec h''
      rw [Bool.false_or]
      refine nat_any_of hi ?_
      rw [ef_eq hi, ← Nat.eq_of_beq_eq_true hb]
      exact eqK_sound (Nat.beq_refl G)
    · rfl

@[expose] noncomputable def tupA (k i : Nat) : Array Nat := unpack 1920 11 (TO (Nat.add (Nat.mul 7 k) i))

theorem cTO {k i : Nat} (hk : k < 120) (hi : i < 7) :
    canonK 1920 11 (mask 11) (1920 * 11) (TO (Nat.add (Nat.mul 7 k) i)) = true :=
  allN_spec (TC.all k hk) i hi

theorem f0_eq {g : Nat} (hg : g < 2) :
    (ruField1920 0)[g]! = unpack 1920 11 (gen2 (RuT1920.L 0) (RuT1920.L 1) g) ∧
    invCand 1920 (ruField1920 0)[g]! = unpack 1920 11 (gen2 (RuLI1920 0) (RuLI1920 1) g) ∧
    canonK 1920 11 (mask 11) (1920 * 11) (gen2 (RuT1920.L 0) (RuT1920.L 1) g) = true ∧
    canonK 1920 11 (mask 11) (1920 * 11) (gen2 (RuLI1920 0) (RuLI1920 1) g) = true := by
  rcases g with _ | _ | g
  · have e := RuCe.f1920 (f := 0) 0 7 0 rfl (by omega : 0 < 7) rfl (by omega)
    exact ⟨e, by rw [e]; exact (invEqK_sound (perm1920 0 (by omega))).1, cLj (j := 0) (by omega),
      cLI0⟩
  · have e := RuCe.f1920 (f := 0) 0 7 1 rfl (by omega : 1 < 7) rfl (by omega)
    exact ⟨e, by rw [e]; exact (invEqK_sound (perm1920 1 (by omega))).1, cLj (j := 1) (by omega),
      cLI1⟩
  · omega

theorem tstep_spec {k : Nat} (hk : k < 120) (h1 : 1 ≤ k) : parT k < k ∧ genT k < 2 ∧
    ∀ i < 7, qc (qc (gen2 (RuT1920.L 0) (RuT1920.L 1) (genT k)) (TO (Nat.add (Nat.mul 7 (parT k)) i)))
        (gen2 (RuLI1920 0) (RuLI1920 1) (genT k)) = TO (Nat.add (Nat.mul 7 k) i) := by
  have h := TS.all k hk
  unfold tstep at h
  rw [beq_false_of_ne (by omega : k ≠ 0), sb_eq, sb_eq] at h
  have h' : bAnd(Nat.blt (parT k) k, bAnd(Nat.blt (genT k) 2, allN 7 (fun i =>
      Nat.beq (qc (qc (gen2 (RuT1920.L 0) (RuT1920.L 1) (genT k))
        (TO (Nat.add (Nat.mul 7 (parT k)) i))) (gen2 (RuLI1920 0) (RuLI1920 1) (genT k)))
        (TO (Nat.add (Nat.mul 7 k) i))))) = true := h
  obtain ⟨hp, h'⟩ := (bAnd_iff _ _).1 h'
  obtain ⟨hg, h'⟩ := (bAnd_iff _ _).1 h'
  exact ⟨lt_of_blt hp, lt_of_blt hg, fun i hi => Nat.eq_of_beq_eq_true (allN_spec h' i hi)⟩

theorem hs : ∀ k, 1 ≤ k → k < 120 → parT k < k ∧ genT k < 2 ∧ ∀ i < 7, tupA k i =
    compA 1920 (compA 1920 (ruField1920 0)[genT k]! (tupA (parT k) i))
      (invCand 1920 (ruField1920 0)[genT k]!) := by
  intro k h1 hk
  obtain ⟨hp, hg, he⟩ := tstep_spec hk h1
  obtain ⟨o1, o2, o3, o4⟩ := f0_eq hg
  refine ⟨hp, hg, fun i hi => ?_⟩
  rw [tupA, tupA, o2, o1, compA_unpack o3 (cTO (by omega) hi),
    compA_unpack (canonK_pcomp o3 (cTO (by omega) hi)) o4]
  exact congrArg (unpack 1920 11) (he i hi).symm

theorem hd : ∀ k < 120, ∀ l < 120, (∀ i < 7, eqA 1920 (tupA k i) (tupA l i) = true) → k = l := by
  intro k hk l hl he
  have heq : ∀ i < 7, TO (Nat.add (Nat.mul 7 k) i) = TO (Nat.add (Nat.mul 7 l) i) := fun i hi => by
    have e := he i hi
    rw [tupA, tupA, eqA1920 (cTO hk hi) (cTO hl hi)] at e
    exact Nat.eq_of_beq_eq_true e
  have hall : ∀ a b, a < 120 → b < a → (∀ i < 7, TO (Nat.add (Nat.mul 7 a) i) =
      TO (Nat.add (Nat.mul 7 b) i)) → False := fun a b ha hb he => by
    have h := allN_spec (TD.all a ha) b hb
    have hk : allN 7 (fun i => Nat.beq (TO (Nat.add (Nat.mul 7 a) i))
        (TO (Nat.add (Nat.mul 7 b) i))) = true :=
      allN_of_forall fun i hi => by rw [he i hi]; exact Nat.beq_refl _
    rw [hk] at h
    exact Bool.false_ne_true h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hall l k hl h fun i hi => (heq i hi).symm
  · exact hall k l hk h heq

theorem h0 : ∀ i < 7, tupA 0 i = ruEF i := fun i hi => by
  rw [ef_eq hi, ← Nat.eq_of_beq_eq_true (allN_spec t0 i hi), tupA]
  congr 2
  exact Nat.zero_add i

theorem hKH : ∀ j < 10, ruSift 1920 (ruField1920 0) ruCFaithfulBase (ruField1920 2)[j]! = true :=
  fun j hj => by
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 (allN_spec kH j hj)
    exact siftK_sound RuSF.bindsF RuSF.pF RuFS.hl (RuSF.bindsK.2.2.2.2.1 j hj)
      (range_of_canonK (allN_spec cKS j hj)) h2

theorem hKX : ∀ j < 10, ∀ i < 7, ruComm1920 (ruField1920 2)[j]! (ruEF i) = true :=
  fun j hj i hi => by
    rw [RuSF.bindsK.2.2.2.2.1 j hj, ef_eq hi, comm_eq (allN_spec cKS j hj) (cRFi hi)]
    exact allN_spec (allN_spec kX j hj) i hi

theorem hX : ∀ i < 7, isInvA 1920 (ruEF i) (invCand 1920 (ruEF i)) = true := fun i hi => by
  obtain ⟨h1, h2⟩ := invEqK_sound (allN_spec rfPerm i hi)
  rw [ef_eq hi, h1]
  exact h2

theorem hXJ : ∀ i < 7, ruSift 1920 (ruField1920 3) ruJBase (ruEF i) = true := fun i hi => by
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 (allN_spec rfSiftJ i hi)
  exact siftK_sound RuSF.bindsJ RuSF.pJ RuJS2.hl (ef_eq hi) (range_of_canonK (cRFi hi)) h2

theorem hKJ : all2 1920 ruKLevels (fun g => !(allLt 6 fun j => ruComm1920 g (ruJF j)) ||
    siftA 1920 ruJLevels (ruBaseArr 1920 ruJBase) 0 g) = true := by
  refine all2_of_rows_imp RuSF.bindsK RuSF.pK RuKS.hl (Nat.le_refl 2) (fun G hG h => ?_)
    (rowsK CJ.all)
  have hA : (allLt 6 fun j => ruComm1920 (unpack 1920 11 G) (ruJF j)) =
      allN 6 (fun j => cm G (RuT1920.L (Nat.add 24 j))) :=
    allLt_eq_allN fun j hj => by
      rw [jf_eq (by omega)]
      exact comm_eq hG (cLj (by omega))
  unfold cjpK at h
  rw [hA]
  cases hc : allN 6 (fun j => cm G (RuT1920.L (Nat.add 24 j)))
  · rfl
  · rw [hc] at h
    have h' : bAnd(Nat.beq (Nat.shiftRight G (1920 * 11)) 0,
        siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuJS2.LR RuJS2.TRI RuJS2.BP 2 0 G) =
          true := h
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h'
    rw [not_true_or]
    exact siftK_sound RuSF.bindsJ RuSF.pJ RuJS2.hl rfl (range_of_canonK hG) h2

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem facts : (ruEArr.size = 7 ∧ ruEPar.size = 7 ∧ ruEGen.size = 7 ∧ ruEArr[0]! = ruZA ∧
      (∀ i < 7, isInvA 4060 ruEArr[i]! (invCand 4060 ruEArr[i]!) = true) ∧
      (∀ i, 1 ≤ i → i < 7 → ruEPar[i]! < i ∧ ruEGen[i]! < 2 ∧
        eqA 4060 ruEArr[i]! (ruConjA ruNGensA[ruEGen[i]!]! ruEArr[ruEPar[i]!]!) = true) ∧
      (∀ i < 7, ∀ g < 2, ∃ j < 7, eqA 4060 (ruConjA ruNGensA[g]! ruEArr[i]!) ruEArr[j]! = true) ∧
      (∀ i < 7, ∀ j < 7, i ≠ j → eqA 4060 ruEArr[i]! ruEArr[j]! = false) ∧
      (∀ i < 7, eqA 4060 ruEArr[i]! (idA 4060) = false) ∧
      (∀ i < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[i]!) (idA 4060) = true) ∧
      (∀ i < 7, ∀ j < 7, i ≠ j →
        ∃ k < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[j]!) ruEArr[k]! = true) ∧
      (∀ i < 7, ∀ j < 7, eqA 4060 (compA 4060 ruEArr[i]! ruEArr[j]!)
        (compA 4060 ruEArr[j]! ruEArr[i]!) = true) ∧
      (∀ i < 7, ruSift 4060 (ruField4060 1) ruCBase ruEArr[i]! = true) ∧
      (∀ i < 7, siftA 1920 ruKLevels (ruBaseArr 1920 ruKBase) 0 (ruEF i) = true) ∧
      (∀ i < 7, ∀ k < 8, eqA 4060 (compA 4060 ruEArr[i]! ruKGensA[k]!)
        (compA 4060 ruKGensA[k]! ruEArr[i]!) = true)
    )
    ∧ (all2 1920 ruKLevels (fun g => !(allLt 8 fun k => ruComm1920 g (ruKF k)) ||
      eqA 1920 g (idA 1920) || (Nat.any 7 fun i _ => eqA 1920 g (ruEF i))) = true
    )
    ∧ (all2 1920 (rawLevels 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase))
      (fun g => !(allLt 7 fun i => ruComm1920 g (ruEF i)) ||
        siftA 1920 ruKLevels (ruBaseArr 1920 ruKBase) 0 g) = true
    )
    ∧ (all2 1920 (rawLevels 1920 (ruField1920 0) (ruBaseArr 1920 ruCFaithfulBase))
      (fun g => !(allLt 6 fun j => ruComm1920 g (ruJF j)) ||
        siftA 1920 ruJLevels (ruBaseArr 1920 ruJBase) 0 g) = true
    ) :=
  ⟨eFacts, zkFacts,
    RuCG.ceAll2 RuSF.facts.1.1 RuSF.facts.2.2.2.1.1 RuSF.facts.1.2 RuSF.facts.2.2.2.1.2.1 hKH hKX
      hX tupA parT genT h0 hs hd,
    RuCG.cjAll2 RuSF.facts.1.1 RuSF.facts.2.2.2.1.1 RuSF.facts.1.2 RuSF.facts.2.2.2.1.2.1 hKH hKX
      hX tupA parT genT h0 hs hd RuSF.facts.2.2.2.2.1.1 hXJ hKJ⟩

end CertificateChecks.KernelSporSch.RuCt

end
