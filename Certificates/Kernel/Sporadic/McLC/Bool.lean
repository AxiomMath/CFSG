module

public import Certificates.Kernel.Sporadic.McLC.GlueGen
public import Certificates.Kernel.Sporadic.McLC.BoolK
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

section Lemmas

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.SmallOddCore CFSG.ClassicalInvolution
open CFSG.KS.SporSch CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3.Native CFSG.KS.Raw CFSG.Sporadic.SmallOddCore.Native

theorem permOK_of_rep {T : Table} {g : Equiv.Perm (Fin 275)} (h : Rep 275 T g) :
    CFSG.Sporadic.SmallOddCore.permOK 275 T = true := by
  unfold CFSG.Sporadic.SmallOddCore.permOK
  apply CFSG.KC.Co2Mem.isInvA_invCand
  · intro i hi
    rw [natArr_getElem!, h i hi]
    exact idx_lt g hi
  · intro i j hi hj e
    rw [natArr_getElem!, natArr_getElem!, h i hi, h j hj, idx_of_lt _ hi, idx_of_lt _ hj] at e
    exact congrArg Fin.val (g.injective (Fin.ext e))

theorem invOK_of_rep {T : Table} {g : Equiv.Perm (Fin 275)} (h : Rep 275 T g) :
    invOK 275 T (invT 275 T) = true := by
  have hR := rep_inv_of h
  unfold invOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, h i hi, hR _ (idx_lt g hi), idx_inv_idx]

theorem allN_beq_of {f g : Nat → Nat} (h : ∀ x < 275, f x = g x) :
    allN 275 (fun x => Nat.beq (f x) (g x)) = true :=
  allN_of fun x hx => by rw [h x hx]; exact Nat.beq_refl _

theorem alP_sq : alP * alP = 1 := by
  apply perm_ext
  intro x hx
  rw [actN_mul, actN_one, actN_alP hx, actN_alP (McLK.inv_facts hx).1]
  exact (McLK.inv_facts hx).2.1

theorem alP_ne : alP ≠ 1 := by
  intro e
  have h : allN 275 (fun x => Nat.beq (r32 McLK.AL x) x) = true :=
    allN_beq_of fun x hx => by rw [← actN_alP hx, e, actN_one]
  have h0 := alMv_ok
  unfold alMv at h0
  rw [h] at h0
  exact Bool.false_ne_true h0

theorem orderOf_alP : orderOf alP = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two, alP_sq]) alP_ne

theorem cm_spec {x : Nat} (hx : x < 275) :
    LJ 0 (r32 McLK.AL x) = r32 McLK.AL (LJ 0 x) ∧ LJ 2 (r32 McLK.AL x) = r32 McLK.AL (LJ 2 x) := by
  have h := allN_spec cmOK_ok x hx
  rw [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem sg_comm_alP {l : Nat} (hl : l = 0 ∨ l = 2) : sg l * alP = alP * sg l := by
  apply perm_ext
  intro x hx
  have hl' : l < 10 := by omega
  rw [actN_mul, actN_mul, actN_alP hx, actN_sg hl' hx, actN_sg hl' (McLK.inv_facts hx).1,
    actN_alP (LJ_lt hl' hx)]
  rcases hl with rfl | rfl
  · exact (cm_spec hx).1
  · exact (cm_spec hx).2

theorem alP_word : alP = wp qK [1, 1, 1, 1, 1, 1, 1] := by
  apply perm_ext
  intro x hx
  have h0 := alOK_ok
  unfold alOK at h0
  rw [actN_alP hx]
  refine (Nat.eq_of_beq_eq_true (allN_spec h0 x hx)).trans ?_
  exact foldr_wp (fun c _ y hy => GK_eq c hy) hx

noncomputable abbrev cmP : Equiv.Perm (Fin 275) := sg 0 * sg 2 * ((sg 0)⁻¹ * (sg 2)⁻¹)

theorem actN_cmP {x : Nat} (hx : x < 275) : actN cmP x = cmV x := by
  have e1 : (sg 0)⁻¹ = sg 1 := (sg_inv (j := 0) (by norm_num)).symm
  have e3 : (sg 2)⁻¹ = sg 3 := (sg_inv (j := 1) (by norm_num)).symm
  unfold cmP
  rw [e1, e3, actN_mul, actN_mul, actN_mul, actN_sg (by norm_num) hx,
    actN_sg (by norm_num) (LJ_lt (by norm_num) hx),
    actN_sg (by norm_num) (LJ_lt (by norm_num) (LJ_lt (by norm_num) hx)),
    actN_sg (by norm_num) (LJ_lt (by norm_num) (LJ_lt (by norm_num) (LJ_lt (by norm_num) hx)))]
  rfl

theorem cmP_ne : cmP ≠ 1 ∧ cmP ≠ alP := by
  have h0 := cmMv_ok
  unfold cmMv at h0
  rw [bAnd_iff] at h0
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h : allN 275 (fun x => Nat.beq (cmV x) x) = true :=
      allN_beq_of fun x hx => by rw [← actN_cmP hx, e, actN_one]
    have h1 := h0.1
    rw [h] at h1
    exact Bool.false_ne_true h1
  · have h : allN 275 (fun x => Nat.beq (cmV x) (r32 McLK.AL x)) = true :=
      allN_beq_of fun x hx => by rw [← actN_cmP hx, e, actN_alP hx]
    have h1 := h0.2
    rw [h] at h1
    exact Bool.false_ne_true h1

theorem rep_cmP : Rep 275
    (compT 275 (compT 275 McLProof.kx McLProof.ky)
      (compT 275 (invT 275 McLProof.kx) (invT 275 McLProof.ky))) cmP :=
  Rep.compT (Rep.compT rep_kx rep_ky) (Rep.compT (rep_inv_of rep_kx) (rep_inv_of rep_ky))

theorem kgens_rep : ∀ g ∈ McLData.kgens, ∃ l, (l = 0 ∨ l = 2) ∧ Rep 275 g (sg l) := by
  intro g hg
  rw [kgens_eq] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨0, Or.inl rfl, rep_kx⟩
  · exact ⟨2, Or.inr rfl, rep_ky⟩

theorem lt32 : (275 : Nat) < 2 ^ 32 := by norm_num

theorem kWords_letters' : ∀ w ∈ McLData.kWords, ∀ l ∈ w, l = 1 ∨ l = 2 := by decide +kernel

theorem sWords_letters : ∀ w ∈ McLData.sWords, ∀ l ∈ w, l = 1 ∨ l = 2 := by decide +kernel

theorem conjWords_letters : ∀ w ∈ McLData.conjWords, ∀ l ∈ w, l = 1 ∨ l = 2 := by decide +kernel

theorem repData_letters' : ∀ p ∈ McLData.repData,
    (∀ l ∈ p.1, l = 1 ∨ l = 2) ∧ ∀ cw ∈ p.2, ∀ l ∈ cw, l = 1 ∨ l = 2 := by decide +kernel

theorem range_of {w : List Nat} (h : ∀ l ∈ w, l = 1 ∨ l = 2) : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2 :=
  fun l hl => by rcases h l hl with rfl | rfl <;> norm_num

theorem rep_word_abT {w : List Nat} (hw : ∀ l ∈ w, l = 1 ∨ l = 2) :
    Rep 275 (wordTbl 275 McLData.abT w) (wp qAB w) :=
  rep_wordTbl' fun l hl => rep_abT (hw l hl)

theorem rep_conj {C R : Table} {c r : Equiv.Perm (Fin 275)} (hC : Rep 275 C c) (hR : Rep 275 R r) :
    Rep 275 (conjT 275 C (invT 275 C) R) (c * r * c⁻¹) :=
  Rep.compT (Rep.compT hC hR) (rep_inv_of hC)

theorem rep_repGens {gs : List Table} (hgs : gs ∈ McLData.repGens) :
    ∀ T ∈ gs, ∃ g : Equiv.Perm (Fin 275), Rep 275 T g := by
  rw [repGens_eq] at hgs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hgs
  obtain ⟨h1, h2⟩ := repData_letters' p hp
  intro T hT
  unfold FG at hT
  rcases List.mem_cons.1 hT with rfl | hT
  · exact ⟨_, rep_word_kgens h1⟩
  · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
    exact ⟨_, rep_conj (rep_word_kgens (h2 cw hcw)) (rep_word_kgens h1)⟩

end Lemmas

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.McLProof
open CFSG.Sporadic.SmallOddCore hiding coverOK
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.ClassicalInvolution.McLData

theorem tables_ok : permOK 275 Ta = true ∧ permOK 275 Tb = true ∧ involOK 275 Ta = true ∧
    invOK 275 Ta (invT 275 Ta) = true :=
  ⟨permOK_of_rep rep_Ta, permOK_of_rep rep_Tb, involOK_of_orderOf lt32 rep_Ta orderOf_alP,
    invOK_of_rep rep_Ta⟩

theorem kgens_ok : kgens.all (permOK 275) = true ∧
    kgens.all (fun g => invOK 275 g (invT 275 g)) = true ∧
    kgens.all (fun g => commTT 275 g Ta) = true ∧ kgens.length = 2 ∧
    (tblEq 275 Ta (wordTbl 275 kgens [1, 1, 1, 1, 1, 1, 1]) = true ∧
      permOK 275 (wordTbl 275 kgens [1, 1, 1, 1, 1, 1, 1]) = true) := by
  have hw : ∀ l ∈ [1, 1, 1, 1, 1, 1, 1], l = 1 ∨ l = 2 := by decide
  have hk := kgens_rep
  refine ⟨List.all_eq_true.2 fun g hg => ?_, List.all_eq_true.2 fun g hg => ?_,
    List.all_eq_true.2 fun g hg => ?_, rfl, ?_, permOK_of_rep (rep_word_kgens hw)⟩
  · obtain ⟨l, -, h⟩ := hk g hg
    exact permOK_of_rep h
  · obtain ⟨l, -, h⟩ := hk g hg
    exact invOK_of_rep h
  · obtain ⟨l, hl, h⟩ := hk g hg
    exact (commTT_iff h rep_Ta).2 (sg_comm_alP hl)
  · exact (tblEq_iff_eq rep_Ta (rep_word_kgens hw)).2 alP_word

theorem words_ok : (∀ w ∈ kWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧ (∀ w ∈ sWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      (∀ w ∈ conjWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      (∀ p ∈ repData, (∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 2) ∧ ∀ cw ∈ p.2, ∀ l ∈ cw, 1 ≤ l ∧ l ≤ 2) ∧
      sgens.all (permOK 275) = true ∧ repTbls.all (permOK 275) = true ∧
      (conjWords.map (wordTbl 275 abT)).all (fun c => permOK 275 c && invOK 275 c (invT 275 c)) =
        true ∧
      (repData.all fun p => p.2.all fun cw => permOK 275 (wordTbl 275 kgens cw) &&
        invOK 275 (wordTbl 275 kgens cw) (invT 275 (wordTbl 275 kgens cw))) = true ∧
      (repGens.all fun gs => gs.all (permOK 275)) = true := by
  refine ⟨fun w hw => range_of (kWords_letters' w hw), fun w hw => range_of (sWords_letters w hw),
    fun w hw => range_of (conjWords_letters w hw),
    fun p hp => ⟨range_of (repData_letters' p hp).1,
      fun cw hcw => range_of ((repData_letters' p hp).2 cw hcw)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine List.all_eq_true.2 fun g hg => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
    exact permOK_of_rep (rep_word_kgens (sWords_letters w hw))
  · refine List.all_eq_true.2 fun g hg => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact permOK_of_rep (rep_word_kgens (repData_letters' p hp).1)
  · refine List.all_eq_true.2 fun g hg => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
    have h := rep_word_abT (conjWords_letters w hw)
    rw [permOK_of_rep h, invOK_of_rep h]
    rfl
  · refine List.all_eq_true.2 fun p hp => List.all_eq_true.2 fun cw hcw => ?_
    have h := rep_word_kgens ((repData_letters' p hp).2 cw hcw)
    rw [permOK_of_rep h, invOK_of_rep h]
    rfl
  · refine List.all_eq_true.2 fun gs hgs => List.all_eq_true.2 fun T hT => ?_
    obtain ⟨g, h⟩ := rep_repGens hgs T hT
    exact permOK_of_rep h

theorem comm_ok : commOK = true ∧ kx ∈ kgens ∧ ky ∈ kgens := by
  refine ⟨?_, by rw [kgens_eq]; exact List.mem_cons_self,
    by rw [kgens_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
  have hc := rep_cmP
  unfold commOK
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · cases e : tblEq 275 (compT 275 (compT 275 kx ky) (compT 275 (invT 275 kx) (invT 275 ky)))
      (idT 275)
    · rfl
    · exact absurd ((tblEq_idT_iff lt32 hc).1 e) cmP_ne.1
  · cases e : tblEq 275 (compT 275 (compT 275 kx ky) (compT 275 (invT 275 kx) (invT 275 ky))) Ta
    · rfl
    · exact absurd ((tblEq_iff_eq hc rep_Ta).1 e) cmP_ne.2

end CertificateChecks.KernelSpor.McLC

end
