module

public import Certificates.Kernel.Fi22Core.Matrix
public import Certificates.Kernel.Fi22Core.Keys
public import Certificates.Kernel.Fi22Core.Tree
public import CFSG.Certificates.Kernel.Fi22.OrbKeysSound
public import CFSG.Certificates.Kernel.Fi22.LettersSound
public import CFSG.Certificates.Kernel.Spor.ConjIndexSound
import Certificates.Kernel.Fi22Core.Edges0
import Certificates.Kernel.Fi22Core.Edges1
import Certificates.Kernel.Fi22Core.Edges2
import Certificates.Kernel.Fi22Core.Edges3
import Certificates.Kernel.Fi22Core.KeysChecks
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PChainSound

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22C.edgeAll CertificateChecks.KernelFi22C.edgeSl 220
#kon_join CertificateChecks.KernelFi22C.sortAll CertificateChecks.KernelFi22C.sortSl 10

namespace CertificateChecks.KernelFi22C

open CFSG.F3.Native CFSG.KS CFSG.KS.F3L CFSG.KS.Fi22L CFSG.KS.Fi22O CFSG.KC.Enum CFSG.KS.PEnum
  CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native

theorem lk_orbT (t : Nat) {y : Nat} (hy : y < 3510) : lk (orbT t) y = orbEntry t y := by
  unfold lk orbT tM
  rw [fld_window orbPacked _ y (nat_lit 42120) (by change 12 * y + 12 ≤ 42120; omega)]
  unfold orbEntry
  congr 2
  change 42120 * t + 12 * y = 12 * (3510 * t + y)
  omega

theorem ap_tab (t : Nat) {y : Nat} (hy : y < 3510) : ap (orbTab t) y = lk (orbT t) y := by
  rw [ap_orbTab hy, lk_orbT t hy]

theorem tree_facts {k : Nat} (hk : k < 3510) :
    lk (orbT 0) k < 3510 ∧ lk (orbT 1) k < 3510 ∧ lk (orbT 0) (lk (orbT 0) k) = k ∧
      (0 < k → lk (orbT 2) k < k ∧ ((lk (orbT 3) k = 1 ∧ lk (orbT 0) (lk (orbT 2) k) = k) ∨
        (lk (orbT 3) k = 2 ∧ lk (orbT 1) (lk (orbT 2) k) = k))) := by
  have h := allN_spec tree_ok k hk
  unfold treeAt invoAt at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨ht, h1, h2, h3⟩ := h
  refine ⟨h1, h2, h3, fun hk0 => ?_⟩
  have e0 : Nat.beq k 0 = false := by
    rw [Bool.eq_false_iff]
    intro e
    exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
  rw [e0, Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, bAnd_iff, Nat.blt_eq] at ht
  obtain ⟨hp, hl⟩ := ht
  refine ⟨hp, ?_⟩
  cases e1 : Nat.beq (lk (orbT 3) k) 1 <;> rw [e1] at hl
  · rw [bAnd_iff, Nat.beq_eq, Nat.beq_eq] at hl
    exact Or.inr hl
  · rw [Nat.beq_eq] at hl
    exact Or.inl ⟨Nat.eq_of_beq_eq_true e1, hl⟩

theorem orb_tree {k : Nat} (hk : k < 3510) (hk0 : 0 < k) : ap orbL.par k < k ∧
    ((ap orbL.lab k = 1 ∧ ap orbL.alpha (ap orbL.par k) = k) ∨
      (ap orbL.lab k = 2 ∧ ap orbL.beta (ap orbL.par k) = k)) := by
  obtain ⟨-, -, -, h⟩ := tree_facts hk
  obtain ⟨hp, hl⟩ := h hk0
  change ap (orbTab 2) k < k ∧ ((ap (orbTab 3) k = 1 ∧ ap (orbTab 0) (ap (orbTab 2) k) = k) ∨
    (ap (orbTab 3) k = 2 ∧ ap (orbTab 1) (ap (orbTab 2) k) = k))
  rw [ap_tab 2 hk, ap_tab 3 hk, ap_tab 0 (by omega), ap_tab 1 (by omega)]
  exact ⟨hp, hl⟩

theorem alpha_get {k : Nat} (hk : k < 3510) : ap orbL.alpha k = lk (orbT 0) k ∧ lk (orbT 0) k < 3510 :=
  ⟨ap_tab 0 hk, (tree_facts hk).1⟩

theorem beta_get {k : Nat} (hk : k < 3510) : ap orbL.beta k = lk (orbT 1) k ∧ lk (orbT 1) k < 3510 :=
  ⟨ap_tab 1 hk, (tree_facts hk).2.1⟩

theorem edge_facts {g k : Nat} (hg : g < 2) (hk : k < 3510) :
    canonF (KL k) = true ∧ edge g k = true := by
  have hs : 110 * g + k / 32 < 220 := by omega
  have h := edgeAll (110 * g + k / 32) hs
  unfold edgeSl at h
  have e1 : Nat.div (110 * g + k / 32) 110 = g := by
    change (110 * g + k / 32) / 110 = g
    omega
  have e2 : Nat.mul (Nat.mod (110 * g + k / 32) 110) 32 = k / 32 * 32 := by
    change (110 * g + k / 32) % 110 * 32 = k / 32 * 32
    congr 1
    omega
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, e1, e2] at h
  have h' := allN_spec h (k % 32) (Nat.mod_lt _ (by norm_num))
  have e3 : Nat.add (k / 32 * 32) (k % 32) = k := by
    change k / 32 * 32 + k % 32 = k
    omega
  rw [Raw.Orb.strictB_eq, e3, Eq.mpr Nat.blt_eq hk, bAnd_iff] at h'
  exact h'

theorem canon_KL {k : Nat} (hk : k < 3510) : Canon (KL k) := canonF_spec (edge_facts (g := 0) (by omega) hk).1

theorem edge_eq {g k : Nat} (hg : g < 2) (hk : k < 3510) :
    mulF (KernelFi22C.GL g) (KL k) = mulF (KL (lk (orbT g) k)) (KernelFi22C.GL g) := by
  have h := (edge_facts hg hk).2
  unfold edge at h
  rw [Raw.Orb.strictB_eq] at h
  exact eqF_iff.1 h

theorem GL_zero : KernelFi22C.GL 0 = LA := rfl
theorem GL_one : KernelFi22C.GL 1 = LB := rfl

theorem rowsWF_unlane {X : V} (h : X.wf = true) : RowsWF (unlane 77 X) :=
  RowsWF.of_canonM (canonM_unlane 77 h)

theorem conj_lane {G Gi Kp Kk : V} (hG : G.wf = true) (hGi : Gi.wf = true)
    (hKk : Kk.wf = true) (hid : mulF G Gi = LI) (he : mulF G Kp = mulF Kk G) :
    conjM 77 (unlane 77 G) (unlane 77 Gi) (unlane 77 Kp) = unlane 77 Kk := by
  have e1 : conjM 77 (unlane 77 G) (unlane 77 Gi) (unlane 77 Kp) =
      mul 77 (mul 77 (unlane 77 Kk) (unlane 77 G)) (unlane 77 Gi) := by
    unfold conjM
    rw [mul_eq' G Kp, he, ← mul_eq']
  rw [e1]
  have hs : (mul 77 (unlane 77 Kk) (unlane 77 G)).size = 77 := by
    unfold mul
    rw [Array.size_map, unlane_size]
  have hw := RowsWF.mul _ 77 (rowsWF_unlane hKk) (rowsWF_unlane hG)
  apply eq_of_canonM (canonM_mul hs hw (canonM_unlane 77 hGi)) (canonM_unlane 77 hKk)
  rw [toMat_mul hs hw (rowsWF_unlane hGi),
    toMat_mul (unlane_size 77 Kk) (rowsWF_unlane hKk) (rowsWF_unlane hG), Matrix.mul_assoc,
    ← toMat_mul (unlane_size 77 G) (rowsWF_unlane hG) (rowsWF_unlane hGi), mul_eq', hid, ← idM_eq,
    toMat_idM, Matrix.mul_one]

theorem conjA {p k : Nat} (hp : p < 3510) (hk : k < 3510) (h : lk (orbT 0) p = k) :
    conjM 77 (matA ()) (matA ()) (unlane 77 (KL p)) = unlane 77 (KL k) := by
  rw [matA_eq]
  have e := edge_eq (g := 0) (by omega) hp
  rw [h, GL_zero] at e
  exact conj_lane canons.1.wf canons.1.wf (canon_KL hk).wf (eqF_iff.1 a2_ok) e

theorem conjB {p k : Nat} (hp : p < 3510) (hk : k < 3510) (h : lk (orbT 1) p = k) :
    conjM 77 (matB ()) (matBi ()) (unlane 77 (KL p)) = unlane 77 (KL k) := by
  rw [matB_eq, matBi_eq]
  have e := edge_eq (g := 1) (by omega) hp
  rw [h, GL_one] at e
  exact conj_lane canons.2.1.wf canons.2.2.1.wf (canon_KL hk).wf (eqF_iff.1 bbi_ok) e

theorem keys_size : orbL.keys.size = 3510 := (orbKeys_spec (orbTab 2) (orbTab 3)).1

theorem keys_get : ∀ k < 3510, orbL.keys[k]! = unlane 77 (KL k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨-, h0, hstep⟩ := orbKeys_spec (orbTab 2) (orbTab 3)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · change (orbKeys (orbTab 2) (orbTab 3))[0]! = _
      rw [h0, matA_eq, eqF_iff.1 root_ok]
    · obtain ⟨hp, hl⟩ := orb_tree hk hk0
      change (orbKeys (orbTab 2) (orbTab 3))[k]! = _
      have hp' : ap (orbTab 2) k < k := hp
      rw [hstep k hk0 hk hp']
      change conjL (ap orbL.lab k) orbL.keys[ap orbL.par k]! = _
      rw [ih _ hp (by omega)]
      unfold conjL
      rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]
        simp only [beq_self_eq_true, ite_true]
        exact conjA (by omega) hk (by rw [← (alpha_get (by omega)).1]; exact h2)
      · rw [h1]
        simp only [show (2 == 1) = false from rfl, Bool.false_eq_true, ite_false]
        exact conjB (by omega) hk (by rw [← (beta_get (by omega)).1]; exact h2)

theorem sort_facts {i : Nat} (hi : i < 3510) : r32 SO i < 3510 ∧ r32 SOI i < 3510 ∧
    r32 SO (r32 SOI i) = i ∧ (i + 1 < 3510 → kx (r32 SO i) < kx (r32 SO (i + 1))) := by
  have hs : i / 351 < 10 := by omega
  have h := sortAll (i / 351) hs
  unfold sortSl at h
  rw [Raw.Orb.strictB_eq] at h
  have h' := allN_spec h (i % 351) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 351) 351) (i % 351) = i := by
    change i / 351 * 351 + i % 351 = i
    omega
  rw [e] at h'
  unfold sortAt at h'
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq,
    Nat.beq_eq] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  refine ⟨h1, h2, h3, fun hi1 => ?_⟩
  rw [Raw.Orb.bIf_eq, ite_eq_left (Nat.blt_eq.mpr hi1), Nat.blt_eq] at h4
  exact h4

theorem sort_mono {a b : Nat} (hab : a < b) (hb : b < 3510) : kx (r32 SO a) < kx (r32 SO b) := by
  induction b with
  | zero => omega
  | succ b ih =>
    have h := (sort_facts (i := b) (by omega)).2.2.2 hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
    · exact lt_trans (ih hab (by omega)) h
    · exact h

theorem kx_inj {j k : Nat} (hj : j < 3510) (hk : k < 3510) (h : kx j = kx k) : j = k := by
  obtain ⟨-, hj1, hj2, -⟩ := sort_facts hj
  obtain ⟨-, hk1, hk2, -⟩ := sort_facts hk
  by_contra hne
  have hne' : r32 SOI j ≠ r32 SOI k := fun e => hne (by rw [← hj2, ← hk2, e])
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · have := sort_mono hlt hk1
    rw [hj2, hk2, h] at this
    exact lt_irrefl _ this
  · have := sort_mono hlt hj1
    rw [hj2, hk2, h] at this
    exact lt_irrefl _ this

theorem kx_of_KL (k : Nat) : kx k = (KL k).p + 2 ^ 5929 * (KL k).m := by
  unfold KL
  rw [strictT_eq]
  change kx k = (kx k &&& mk 5929) + 2 ^ 5929 * (kx k >>> 5929)
  rw [mk_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.mod_add_div]

theorem keys_inj : ∀ i < orbL.keys.size, ∀ j < orbL.keys.size,
    keyOf orbL.keys[i]! = keyOf orbL.keys[j]! → i = j := by
  intro i hi j hj e
  rw [keys_size] at hi hj
  have e' := keyOf_inj e
  rw [keys_get i hi, keys_get j hj] at e'
  have ci := canon_KL hi
  have cj := canon_KL hj
  have e2 := unlane_inj ci.p ci.m cj.p cj.m e'
  apply kx_inj hi hj
  rw [kx_of_KL, kx_of_KL, e2]

theorem check_at {k : Nat} (hk : k < 3510) :
    conjCheckAt 77 (matA ()) (matA ()) (matB ()) (matBi ()) orbL
      (fun X => (indexOf orbL.keys).getD (keyOf X) orbL.keys.size) k = true := by
  obtain ⟨ha, ha'⟩ := alpha_get hk
  obtain ⟨hb, hb'⟩ := beta_get hk
  have hpos : (indexOf orbL.keys).getD (keyOf orbL.keys[k]!) orbL.keys.size = k :=
    indexOf_getD keys_inj (by rw [keys_size]; exact hk)
  unfold conjCheckAt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, hpos⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [keys_get k hk]
    exact canonM_unlane 77 (canon_KL hk).wf
  · rw [keys_size, ha]
    exact ha'
  · rw [ha, keys_get k hk, keys_get _ ha', conjA hk ha' rfl]
    exact eqM_self (unlane_size 77 _)
  · rw [keys_size, hb]
    exact hb'
  · rw [hb, keys_get k hk, keys_get _ hb', conjB hk hb' rfl]
    exact eqM_self (unlane_size 77 _)
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Or.inl rfl
    · right
      obtain ⟨hp, hl⟩ := orb_tree hk hk0
      exact ⟨hp, hl⟩

theorem conj_ok (chunks : Nat) : conjOrbitOK 77 (matA ()) (matA ()) (matB ()) (matBi ()) orbL chunks = true := by
  unfold conjOrbitOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by rw [keys_size]; norm_num, by rw [keys_size]; norm_num⟩, ?_⟩, ?_⟩
  · rw [keys_get 0 (by norm_num), eqF_iff.1 root_ok, ← matA_eq]
    exact eqM_self (by rw [matA_eq]; exact unlane_size 77 _)
  · exact CFSG.KS.PC.parAll_of fun k hk => check_at (by rwa [keys_size] at hk)

end CertificateChecks.KernelFi22C

end
