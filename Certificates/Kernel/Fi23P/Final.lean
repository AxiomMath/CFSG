module

public import Certificates.Kernel.Fi23P.Group
public import Certificates.Kernel.Fi23M.Keys
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Fi23R.Sound
import Certificates.Kernel.Fi23P.Neg
import Mathlib
public import CFSG.Sporadic.Fi23.Class

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23P CFSG.KD.Fi23K CFSG.KD.Fi23P CFSG.KS.TW
  CFSG.Sporadic.Th.Native CFSG.Monster.Existence.Fi23Sp8.Native CFSG.KS.Raw.Orb
  CFSG.Sporadic.Bridge.Fi23GPL.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CertificateChecks.KernelFi23C CFSG.KC.Fi23R

theorem labA_size : labA.size = 31671 := by unfold labA; simp
theorem parA_size : parA.size = 31671 := by unfold parA; simp
theorem genA_size : genA.size = 31671 := by unfold genA; simp
theorem vecA_size : vecA.size = 31671 := by unfold vecA; simp

theorem SK_roots : SK.roots = #[4777, 16688, 0] := by unfold SK; rfl
theorem SK_lab : SK.lab = labA := by unfold SK; rfl
theorem SK_par : SK.par = parA := by unfold SK; rfl
theorem SK_gen : SK.gen = genA := by unfold SK; rfl
theorem SK_vec : SK.vec = vecA := by unfold SK; rfl
theorem SK_ptOf : SK.ptOf = ptA := by unfold SK; rfl

theorem roots_get {c : Nat} (hc : c < 3) : (#[4777, 16688, 0] : Array Nat)[c]! = rtP c := by
  interval_cases c <;> rfl

theorem SOK_mk (v pt : Array Nat) : SOK ⟨#[4777, 16688, 0], labA, parA, genA, v, pt⟩ := by
  unfold SOK
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pathW_fun : pathW SK = pathK := funext (pathW_eq SK_ok)

section


theorem evalWord_fun : evalWord IT IV = wK := funext fun w => funext fun q => evalWord_eq w q

theorem conjAct_fun : conjAct IT IV = conjK := funext fun u => funext fun q => conjAct_eq u q

theorem stabWord_fun : stabWord IT SK = stabK := by
  funext c pr
  unfold stabWord stabK
  rw [SK_par, SK_gen, SK_roots, pathWord_eq, pathWord_eq, IT_ap]
  rfl

theorem search_eq : search G4 IT IV = SK := by
  unfold search
  simp only [piPt0, piPt8, List.toList_toArray, orb_eq]
  rw [commPt_eq (SOK_mk #[] #[]), sigList_eq (SOK_mk #[] #[]), basis_ok, vecs_eq]
  simp only [vecA_get]
  unfold SK
  exact congrArg (Search.mk #[4777, 16688, 0] labA parA genA vecA) ptOf_eq

theorem imgConj_ok : imgConjOK () = true := by
  unfold imgConjOK
  rw [Bool.and_eq_true, imgWords_size, List.all_eq_true]
  refine ⟨rfl, fun k hk => ?_⟩
  have hk' := List.mem_range.1 hk
  rw [prefWord_eq hk', imgWords_get hk']
  exact List.all_eq_true.1 conj_ok k hk

theorem root_ok : rootCheck G4 SK = true := by
  unfold rootCheck
  rw [piPt0, piPt8, SK_roots, SK_lab, SK_par, SK_gen, labA_size, parA_size, genA_size,
    beq_self_eq_true]
  simp only [labA_get]
  quickRfl

theorem pi_lab : (gIdx ()).all (fun k => labG (piL.getD k 0) == 0) = true := by quickRfl

theorem lab_ok : labCheck G4 IT SK = true := by
  unfold labCheck
  rw [SK_lab]
  simp only [labA_get, IT_ap]
  rw [Bool.and_eq_true, allIn_iff, List.all_eq_true]
  refine ⟨fun p hp => ?_, fun k hk => ?_⟩
  · rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, labG_eq hp]
    refine ⟨lab_lt hp, fun k hk => ?_⟩
    have hk' := mem_gIdx.1 hk
    rw [XK_eq ((gOK_iff k).1 hk').1 hp, labG_eq (x := tb G k p) (TG_lt hk' hp), beq_iff_eq]
    exact lab_T hp hk'
  · rw [piPt_eq ((gOK_iff k).1 (mem_gIdx.1 hk)).1]
    exact List.all_eq_true.1 pi_lab k hk

theorem path_ok : pathCheck IT IV SK = true := by
  unfold pathCheck
  rw [evalWord_fun, pathW_fun, SK_roots, SK_lab]
  simp only [labA_get]
  rw [allIn_iff]
  intro p hp
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  have e : pathK p = pathF (rtP (labP p)) 100 p := by
    unfold pathK
    rw [labG_eq hp, rootsA_get (lab_lt hp)]
  rw [e, labG_eq hp, roots_get (lab_lt hp)]
  obtain ⟨h1, h2⟩ := path_spec 100 p hp (dep_lt hp)
  refine ⟨h1, fun z hz => ?_⟩
  obtain ⟨g, hg, rfl⟩ := h2 z hz
  have := (gOK_iff g).1 hg
  unfold letterOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  omega

theorem vec_k1 : allN 255 (fun i => strictB (tb L 7 i) fun p => bAnd(Nat.ble 1 (vecG p),
    bAnd(Nat.ble (vecG p) 255, Nat.beq ptA[vecG p]! p))) = true := by quickRfl

theorem vec_k2 : allN 256 (fun v => bIf(Nat.beq v 0, true, bAnd(Nat.blt ptA[v]! 31671,
    bAnd(Nat.beq (labG ptA[v]!) 0, Nat.beq (vecG ptA[v]!) v)))) = true := by quickRfl

theorem ptA_size : ptA.size = 256 := by simp [ptA]

theorem allIn_one {p : Nat → Bool} (h : ∀ v, 1 ≤ v → v < 256 → p v = true) :
    allIn 1 256 p = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨k, hk⟩ _
  exact h (1 + k) (by omega) (by omega)

theorem vecC_ok : vecCheck SK = true := by
  unfold vecCheck
  rw [sigList_eq SK_ok, SK_vec, SK_ptOf, SK_lab, vecA_size, ptA_size, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨rfl, rfl⟩, fun p hp => ?_⟩, allIn_one fun v hv1 hv2 => ?_⟩
  · unfold sigL at hp
    rw [List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    have h := allN_iff.1 vec_k1 i (List.mem_range.1 hi)
    rw [strictB_eq, bAnd_eq, bAnd_eq] at h
    simp only [Bool.and_eq_true] at h ⊢
    rw [vecA_get]
    exact ⟨⟨decide_eq_true (Nat.le_of_ble_eq_true h.1), decide_eq_true (Nat.le_of_ble_eq_true h.2.1)⟩,
      beq_iff_eq.2 (Nat.eq_of_beq_eq_true h.2.2)⟩
  · have h := allN_iff.1 vec_k2 v hv2
    have hv0 : ¬ Nat.beq v 0 = true := fun e => by have := Nat.eq_of_beq_eq_true e; omega
    rw [bIf_eq, if_neg hv0, bAnd_eq, bAnd_eq] at h
    simp only [Bool.and_eq_true] at h ⊢
    rw [vecA_get, labA_get]
    exact ⟨⟨decide_eq_true (by simpa [Nat.blt_eq] using h.1), beq_iff_eq.2 (Nat.eq_of_beq_eq_true h.2.1)⟩,
      beq_iff_eq.2 (Nat.eq_of_beq_eq_true h.2.2)⟩

theorem vecG_eq {x : Nat} (hx : x < 31671) (h0 : labP x = 0) : vecG x = tb L 5 x := by
  unfold vecG
  rw [if_pos ⟨hx, h0⟩]

theorem trans_ok' : transCheck IT IV SK = true := by
  unfold transCheck
  rw [sigList_eq SK_ok, conjAct_fun, pathW_fun, SK_vec]
  simp only [vecA_get]
  rw [List.all_eq_true]
  intro p hp
  rw [List.all_eq_true]
  intro q hq
  obtain ⟨hp1, hp2⟩ := mem_sigL.1 hp
  obtain ⟨hq1, hq2⟩ := mem_sigL.1 hq
  rw [beq_iff_eq, ← conj_cp hp1 hp2 q hq1]
  obtain ⟨t1, t2⟩ := trans_cp 100 p hp1 hp2 (dep_lt hp1) q hq1 hq2
  rw [vecG_eq (Fin.isLt _) t1, vecG_eq hp1 hp2, vecG_eq hq1 hq2, t2]
  rfl

theorem sep_ok : sepCheck IT IV SK = true := by
  unfold sepCheck
  dsimp only
  rw [sigList_eq SK_ok, commPt_eq SK_ok, evalWord_fun, stabWord_fun, SK_roots, SK_lab]
  simp only [labA_get]
  rw [List.all_eq_true]
  intro c hc
  have hc3 := List.mem_range.1 hc
  rw [roots_get hc3, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · have h := stab_ok c hc3
    rw [rootsA_get hc3] at h
    exact h
  · rw [allIn_iff]
    intro y hy
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · by_cases h : (sigL.all fun p => commK p y == commK p (rtP c)) = true
      · rw [Bool.or_eq_true]
        right
        rw [beq_iff_eq, labG_eq hy]
        exact sep_lab hy hc3 h
      · rw [Bool.or_eq_true]
        left
        rw [Bool.not_eq_true']
        exact Bool.eq_false_iff.2 h
    · by_cases h : (labG y == c && ((stabPairs c).map (stabK c)).all fun w => wK w y == y) = true
      · rw [Bool.or_eq_true]
        right
        rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
        rw [beq_iff_eq]
        exact sep_root hy hc3 (by rw [← labG_eq hy]; exact h.1) fun w hw => beq_iff_eq.1 (h.2 w hw)
      · rw [Bool.or_eq_true]
        left
        rw [Bool.not_eq_true']
        exact Bool.eq_false_iff.2 h

theorem gen_ok : genCheck (dTable orbLit) SK = true := by
  unfold genCheck
  rw [SK_lab, dTable_ap (by norm_num)]
  simp only [labA_get]
  quickRfl

theorem count_c {c N : Nat} (h : Nat.beq (cntS (fun p => Nat.beq (labP p) c) 0 31671) N = true) :
    (List.range 31671).countP (fun p => labG p == c) = N := by
  have h' := Nat.eq_of_beq_eq_true h
  rw [CertificateChecks.KernelFi23R.cntS_eq] at h'
  simp only [Nat.zero_add, List.map_id'] at h'
  rw [← h']
  apply List.countP_congr
  intro x hx
  rw [labG_eq (List.mem_range.1 hx)]
  simp

theorem count_ok : countCheck SK = true := by
  unfold countCheck
  rw [SK_lab]
  simp only [labA_get]
  rw [List.all_eq_true]
  intro c hc
  have hc3 := List.mem_range.1 hc
  rw [beq_iff_eq]
  interval_cases c
  · exact count_c cnt_ok0
  · exact count_c cnt_ok1
  · exact count_c cnt_ok2

theorem sp8_true : sp8Entry () = true := by
  have e : sp8Entry () = sp8Checks G4 IT IV (dTable orbLit) (search G4 IT IV) := by
    unfold sp8Entry sp8FromOrbit sp8Tab sp8Inv sp8Run
    rw [CFSG.KD.Fi23K.orbitData_eq']
  rw [e, search_eq]
  unfold sp8Checks
  rw [imgConj_ok, root_ok, lab_ok, path_ok, vecC_ok, trans_ok', sep_ok, gen_ok, count_ok]
  rfl

end

end CertificateChecks.KernelFi23P

end
