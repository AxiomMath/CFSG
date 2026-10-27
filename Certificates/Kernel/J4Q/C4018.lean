module

public import CFSG.Sporadic.J4.QTOutActNative
public import CFSG.Sporadic.J4.QTNative
public import CFSG.Sporadic.J4.QTRankNative
public import Certificates.Kernel.J4Q.Mask
public import Certificates.Kernel.J4Q.MaskRep
public import Certificates.Kernel.J4Q.C4018K
public import CFSG.Sporadic.J4.QTOutActNative
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.QTBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT

theorem orB_false (b : Bool) : orB false b = b := rfl

@[expose] noncomputable def mkAll (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

theorem mkAll_eq (f : Nat → Bool) : ∀ l : List Nat, mkAll l f = l.all f
  | [] => rfl
  | x :: l => by
    change andB (f x) (mkAll l f) = _
    rw [mkAll_eq f l, List.all_cons]
    cases f x <;> rfl

theorem mkAll_spec {l : List Nat} {f : Nat → Bool} (h : mkAll l f = true) : ∀ x ∈ l, f x = true := by
  rw [mkAll_eq, List.all_eq_true] at h
  exact h

theorem contains_mkSet (l : List Nat) (x : Nat) : l.contains x = bitB (mkSet l) x := by
  rw [bitB_eq, Bool.eq_iff_iff, ← mem_mkSet, List.contains_iff_mem]

@[expose] noncomputable def mkO1 : List Nat := fstsK (ptsK OR.s0)

@[expose] noncomputable def mkO2 : List Nat := fstsK (ptsK OR.s1)

theorem o1_eq : o1 = mkO1 := by
  rw [mkO1, fstsK_eq, ← ptsOfString_ofList]
  unfold o1
  rw [OR.eq]
  rfl

theorem o2_eq : o2 = mkO2 := by
  rw [mkO2, fstsK_eq, ← ptsOfString_ofList]
  unfold o2
  rw [OR.eq]
  rfl

theorem orb_chk : andB (Nat.beq (lenK mkO1) 276) (andB (mkNodup mkO1) (andB (Nat.beq (lenK mkO2) 1771)
    (andB (mkNodup mkO2) (andB (allLtK 2048 (mkO1 ++ mkO2))
      (andB (notB (bitB (mkSet (mkO1 ++ mkO2)) 0))
        (andB (Nat.beq (mkSet (mkO1 ++ mkO2)) (mkSet (List.range' 1 2047)))
          (andB (strictB (mkSet mkO2) fun S => mkAll mkO1 fun c => notB (bitB S c))
            (andB (bitB (mkSet mkO1) 1) (bitB (mkSet mkO2) 3))))))))) = true := by
  quickRfl

theorem close1_chk :
    (strictB (mkSet mkO1) fun S => mkAll mkO1 fun c => letters.all fun ℓ =>
      bitB S (actN 11 (letterRows.getD (letters.idxOf ℓ) []) c)) = true := by
  quickRfl

theorem close2_chk :
    (strictB (mkSet mkO2) fun S => mkAll mkO2 fun c => letters.all fun ℓ =>
      bitB S (actN 11 (letterRows.getD (letters.idxOf ℓ) []) c)) = true := by
  quickRfl

theorem tp23_chk : decide (tp 23 = idT ∧ ∀ n ∈ List.range 23, lenOK (mkTPL.getD n []) = true) = true := by
  quickRfl

theorem id_chk : CFSG.KC.Enum.allN 2048 (fun c => actN 11 idT c == c) = true := by quickRfl

@[expose] noncomputable def mkKI2 : List Nat := (List.range 11).map fun j => getN 0 mkKINV (2 ^ j)

@[expose] def mkFTi (i : Nat) : Bool :=
  decide (∀ j ∈ List.range 11, mkFT.getD (11 * i + j) [] = compT (mkTPL.getD i []) (powT hT j))

#j4q_all CFSG.KD.J4Q.FTC CertificateChecks.KernelJ4Q.mkFTi 23

theorem mkFT_length : mkFT.length = 253 := by
  rw [← lenK_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem mem_fTabs {t : List Nat} (h : t ∈ mkFT) : t ∈ fTabs := by
  obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem h
  have hx' : x < 253 := mkFT_length ▸ hx
  have hi : x / 11 < 23 := by omega
  have hj : x % 11 < 11 := Nat.mod_lt _ (by decide)
  have h1 := of_decide_eq_true (FTC.all (x / 11) hi) (x % 11) (List.mem_range.2 hj)
  rw [Nat.div_add_mod, List.getD_eq_getElem _ _ hx, ← tp_eq hi] at h1
  rw [h1]
  unfold fTabs
  exact List.mem_flatMap.2 ⟨x / 11, List.mem_range.2 hi,
    List.mem_map.2 ⟨x % 11, List.mem_range.2 hj, rfl⟩⟩

@[expose] noncomputable def mkCand (s w : Nat) : List Nat :=
  (List.range 11).map fun j => actN 11 ((List.range 11).map fun i =>
    actN 11 (getL mkTPL ((s * i) % 23)) w) (getN 0 mkKI2 j)

theorem cand_eq (s w : Nat) : candTab s w = mkCand s w := by
  unfold candTab mkCand
  rw [tpL_eq]
  simp only [actT_eq, rowsXor_eq, getL_eq]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.1 hj
  have hp : 2 ^ j < 2048 := by
    calc 2 ^ j < 2 ^ 11 := Nat.pow_lt_pow_right (by decide) hj'
      _ = 2048 := by decide
  rw [kinv_getD hp, mkKI2, getN_zero_eq (List.map _ _), List.getD_eq_getElem _ _ (by simpa using hj')]
  simp

@[expose] noncomputable def mkSV (s : Nat) : Bool :=
  orB (Nat.beq s 0) (strictB (mkSet mkO1) fun S => mkAll mkO1 fun w =>
    orB (notB (mkAll mkO1 fun c => bitB S (actN 11 (mkCand s w) c))) (mkFT.contains (mkCand s w)))

#j4q_all CFSG.KD.J4Q.SVC CertificateChecks.KernelJ4Q.mkSV 23

theorem surv_eq (s w : Nat) :
    survOK s w = mkAll mkO1 fun c => bitB (mkSet mkO1) (actN 11 (mkCand s w) c) := by
  unfold survOK
  rw [o1_eq, cand_eq, mkAll_eq]
  simp only [contains_mkSet, actT_eq]

theorem hWord_chk : decide (∀ ℓ ∈ hWord, ℓ ∈ letters) = true := by quickRfl

theorem orbits_chk : decide (orbits.length = 2 ∧ (orbits.getD 0 (0, [], [])).1 = 1 ∧
    (orbits.getD 1 (0, [], [])).1 = 3) = true := by
  quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem c4018 : (orbits.length = 2 ∧ (orbits.getD 0 (0, [], [])).1 = 1 ∧
          (orbits.getD 1 (0, [], [])).1 = 3)
    ∧ (o1.length = 276 ∧ o1.Nodup)
    ∧ (o2.length = 1771 ∧ o2.Nodup)
    ∧ (∀ c ∈ o1 ++ o2, c < 2 ^ 11 ∧ c ≠ 0)
    ∧ (∀ c < 2 ^ 11, c ≠ 0 → c ∈ o1 ∨ c ∈ o2)
    ∧ (∀ c ∈ o1, c ∉ o2)
    ∧ (1 ∈ o1 ∧ 3 ∈ o2)
    ∧ ((∀ c ∈ o1, ∀ ℓ ∈ letters, act ℓ c ∈ o1) ∧ ∀ c ∈ o2, ∀ ℓ ∈ letters, act ℓ c ∈ o2)
    ∧ (∀ c < 2 ^ 11, actT (tp 23) c = c)
    ∧ (∀ n < 23, lenOK (tp n) = true)
    ∧ (∀ c < 2 ^ 11, kcomb (kinv.getD c 0) = c ∧ kinv.getD c 0 < 2 ^ 11)
    ∧ (∀ ℓ ∈ hWord, ℓ ∈ letters)
    ∧ (∀ s < 23, s ≠ 0 → ∀ w ∈ o1, survOK s w = true → survIn s w = true) := by
  obtain ⟨l1, h⟩ := andB_true orb_chk
  obtain ⟨n1, h⟩ := andB_true h
  obtain ⟨l2, h⟩ := andB_true h
  obtain ⟨n2, h⟩ := andB_true h
  obtain ⟨lt, h⟩ := andB_true h
  obtain ⟨nz, h⟩ := andB_true h
  obtain ⟨cov, h⟩ := andB_true h
  obtain ⟨dis, h⟩ := andB_true h
  obtain ⟨m1, m3⟩ := andB_true h
  have c1 := close1_chk
  have c2 := close2_chk
  rw [mkStrictB_eq] at c1 c2 dis
  obtain ⟨t23, tlen⟩ := of_decide_eq_true tp23_chk
  refine ⟨of_decide_eq_true orbits_chk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    of_decide_eq_true hWord_chk, ?_⟩
  · rw [o1_eq, ← lenK_eq]
    exact ⟨Nat.eq_of_beq_eq_true l1, nodup_of_mkNodup n1⟩
  · rw [o2_eq, ← lenK_eq]
    exact ⟨Nat.eq_of_beq_eq_true l2, nodup_of_mkNodup n2⟩
  · rw [o1_eq, o2_eq]
    intro c hc
    refine ⟨allLtK_spec lt c hc, fun h0 => ?_⟩
    subst h0
    rw [mem_mkSet, ← bitB_eq] at hc
    rw [hc] at nz
    exact absurd nz (by decide)
  · intro c hc h0
    rw [o1_eq, o2_eq, ← List.mem_append]
    exact mem_of_mkSet_eq cov (List.mem_range'_1.2 ⟨Nat.pos_of_ne_zero h0, by simpa using hc⟩)
  · rw [o1_eq, o2_eq]
    intro c hc hc2
    have h := mkAll_spec dis c hc
    rw [mem_mkSet, ← bitB_eq] at hc2
    rw [hc2] at h
    exact absurd h (by decide)
  · rw [o1_eq, o2_eq, mem_mkSet, mem_mkSet, ← bitB_eq, ← bitB_eq]
    exact ⟨m1, m3⟩
  · rw [o1_eq, o2_eq]
    refine ⟨fun c hc ℓ hℓ => ?_, fun c hc ℓ hℓ => ?_⟩
    · rw [mem_mkSet, ← bitB_eq, act_eq]
      exact List.all_eq_true.1 (mkAll_spec c1 c hc) ℓ hℓ
    · rw [mem_mkSet, ← bitB_eq, act_eq]
      exact List.all_eq_true.1 (mkAll_spec c2 c hc) ℓ hℓ
  · intro c hc
    rw [t23, actT_eq]
    exact beq_iff_eq.1 (CFSG.KS.allN_spec id_chk c (by simpa using hc))
  · intro n hn
    rw [tp_eq hn]
    exact tlen n (List.mem_range.2 hn)
  · intro c hc
    have hc' : c < 2048 := by simpa using hc
    have h := mkAllI_spec kinvv_chk c (mkKINV_length ▸ hc')
    rw [Nat.zero_add, Bool.and_eq_true, beq_iff_eq] at h
    rw [kinv_getD hc', kcomb_eq, getN_zero_eq]
    exact ⟨h.1, by simpa using mkLt h.2⟩
  · intro s hs hs0 w hw hsurv
    have h := SVC.all s hs
    unfold mkSV at h
    rw [nbeq_false hs0, orB_false, mkStrictB_eq] at h
    rw [o1_eq] at hw
    have h2 := mkAll_spec h w hw
    rw [← surv_eq, hsurv] at h2
    unfold survIn
    rw [cand_eq, List.contains_iff_mem]
    exact mem_fTabs (List.contains_iff_mem.1 h2)

end CertificateChecks.KernelJ4Q

end
