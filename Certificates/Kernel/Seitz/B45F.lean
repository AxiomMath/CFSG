module

public import Certificates.Kernel.Seitz.B45T
public import CFSG.Certificates.Kernel.Seitz77B45Sound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
import CFSG.Certificates.Kernel.LocalQTRestrSound
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

namespace CertificateChecks.KernelSeitz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.SeitzB45
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.Seitz77CaseB45
open CFSG.KC.L34KSnd

theorem t_parts : TLE.cnt = 256 ∧ etl = penumRec 42 6 256 TLE.T TLE.PL ∧
    enumOK 42 tlGens etl = true ∧ ∀ i < 256, canonK 42 6 (mask 6) (42 * 6) (TLE.T i) = true := by
  obtain ⟨a1, a2, a3⟩ := (by simpa only [bAnd_iff] using t_hd :
    gensK tlGens 42 6 TLE.k TLE.G = true ∧ Nat.beq TLE.cnt 256 = true ∧
      penumHdK (pidn 42 6) TLE.cnt 256 TLE.T TLE.PL = true)
  have e : TLE.cnt = 256 := Nat.eq_of_beq_eq_true a2
  have hp : ∀ i < TLE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false TLE.G TLE.GI TLE.k TLE.cnt TLE.T
      TLE.PL TLE.POS TLE.SRT TLE.SRI i = true := fun i hi =>
    penumSl_spec t_sl i (Nat.zero_le _) (by omega) hi
  have hs := penumK_left_sound (cap := 256) (by decide) (gensOK_of a1) a3 hp
  have he : etl = enumBFS 42 tlGens 256 := rfl
  rw [e] at hs hp
  refine ⟨e, he.trans hs.1, by rw [he, hs.1]; exact hs.2, fun i hi => penumPt_canon (hp i hi)⟩

theorem u_parts : UE.cnt = 64 ∧ eu = penumRec 42 6 64 UE.T UE.PL ∧
    ∀ i < 64, canonK 42 6 (mask 6) (42 * 6) (UE.T i) = true := by
  obtain ⟨a1, a2, a3⟩ := (by simpa only [bAnd_iff] using u_hd :
    gensK uGens 42 6 UE.k UE.G = true ∧ Nat.beq UE.cnt 64 = true ∧
      penumHdK (pidn 42 6) UE.cnt 64 UE.T UE.PL = true)
  have e : UE.cnt = 64 := Nat.eq_of_beq_eq_true a2
  have hp : ∀ i < UE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false UE.G UE.GI UE.k UE.cnt UE.T
      UE.PL UE.POS UE.SRT UE.SRI i = true := fun i hi =>
    penumSl_spec u_sl i (Nat.zero_le _) (by omega) hi
  have hs := penumK_left_sound (cap := 64) (by decide) (gensOK_of a1) a3 hp
  have he : eu = enumBFS 42 uGens 64 := rfl
  rw [e] at hs hp
  exact ⟨e, he.trans hs.1, fun i hi => penumPt_canon (hp i hi)⟩

theorem etl_size : etl.tabs.size = 256 := by
  rw [t_parts.2.1, penumRec_eq, Array.size_ofFn]

theorem etl_get {i : Nat} (hi : i < 256) : etl.tabs[i]! = unpack 42 6 (TLE.T i) := by
  rw [t_parts.2.1, penumRec_eq, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem eu_size : eu.tabs.size = 64 := by
  rw [u_parts.2.1, penumRec_eq, Array.size_ofFn]

theorem eu_get {i : Nat} (hi : i < 64) : eu.tabs[i]! = unpack 42 6 (UE.T i) := by
  rw [u_parts.2.1, penumRec_eq, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem etl_nodup : etl.tabs.toList.Nodup := by
  have h := t_parts.2.2.1
  unfold enumOK at h
  exact (treeOK_spec h).2.2.1

theorem mul_parts {i j : Nat} (hi : i < 256) (hj : j < 256) :
    mtT i j < 256 ∧ pcomp 42 6 (mask 6) (TLE.T i) (TLE.T j) = TLE.T (mtT i j) := by
  have hc : i / 64 < 4 := by omega
  have h := allN_spec (allN_spec (by
    have := (show ∀ c < 4, mulK c = true by
      intro c hc
      interval_cases c
      exacts [mulK0, mulK1, mulK2, mulK3]) (i / 64) hc
    exact this) (i % 64) (Nat.mod_lt _ (by omega))) j hj
  have e : 64 * (i / 64) + i % 64 = i := Nat.div_add_mod i 64
  rw [e, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem mtF_eq (i j : Nat) : mtF i j = mtT i j := by
  unfold mtF mtT mtB
  by_cases hk : 256 * i + j < 65536
  · rw [if_pos hk]
    set k := 256 * i + j
    have hi : k / 256 < 256 := by omega
    have hj : k % 256 < 256 := Nat.mod_lt _ (by omega)
    have ek : k / 256 * 256 + k % 256 = k := by omega
    have hm := mtArr_get.2 _ _ hi hj
    rw [ek, etl_get hi, etl_get hj, comp_unpack' (t_parts.2.2.2 _ hi) (t_parts.2.2.2 _ hj)] at hm
    obtain ⟨hlt, hmul⟩ := mul_parts hi hj
    rw [hmul, ← etl_get hlt, show idxTL = indexOf etl.tabs from rfl,
      CFSG.KC.Restr.posOf_eq etl_nodup (by rw [etl_size]; exact hlt)] at hm
    rw [hm]
    unfold mtT mtB
    have ek' : 256 * (k / 256) + k % 256 = k := by omega
    rw [ek', if_pos hk]
  · rw [if_neg hk, getElem!_neg _ _ (by rw [mtArr_get.1]; exact hk)]
    rfl

theorem bind_parts :
    (∀ i < 256, ((List.range 256).find? fun j => mtT i j == 0).getD 0 = invT i) ∧
    (∀ i < 256, isUT i = (List.range 64).any fun k => Nat.beq (UE.T k) (TLE.T i)) ∧
    (∀ k < 64, ∃ i < 256, TLE.T i = UE.T k) ∧
    (∀ i < 256, ((List.range 256).find? fun j => isUT (mtT (invT j) i)).getD i = repT i) ∧
    ((List.range 256).filter fun i => repT i == i) = [rsT 0, rsT 1, rsT 2, rsT 3] ∧
    (∀ i < 256, ([rsT 0, rsT 1, rsT 2, rsT 3].findIdx? (· == repT i)).getD 0 = labT i) := by
  have h := k_bind
  unfold bindK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, fun k hk => ?_, h4, h5, h6⟩
  obtain ⟨i, hi, he⟩ := List.any_eq_true.1 (h3 k hk)
  exact ⟨i, List.mem_range.1 hi, Nat.eq_of_beq_eq_true he⟩

theorem range_get {α : Type} [Inhabited α] (f : Nat → α) {i : Nat} (hi : i < 256) :
    ((Array.range 256).map f)[i]! = f i := by
  rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_map, Array.getElem_range]

theorem invArr_eq (i : Nat) : invArr[i]! = invT i := by
  unfold invArr
  by_cases hi : i < 256
  · rw [range_get _ hi, ← bind_parts.1 i hi]
    simp only [mtF_eq]
  · rw [getElem!_neg _ _ (by simpa using hi)]
    unfold invT vB
    rw [if_neg hi]
    rfl

theorem isUArr_eq (i : Nat) : isUArr[i]! = isUT i := by
  unfold isUArr
  by_cases hi : i < 256
  · rw [getElem!_pos _ _ (by simpa [etl_size] using hi), Array.getElem_map,
      ← getElem!_pos etl.tabs i (by rw [etl_size]; exact hi), etl_get hi, bind_parts.2.1 i hi,
      Bool.eq_iff_iff, Array.contains_iff_mem, List.any_eq_true]
    constructor
    · intro hm
      obtain ⟨k, hk, he⟩ := Array.getElem_of_mem hm
      have hk' : k < 64 := by rwa [eu_size] at hk
      refine ⟨k, List.mem_range.2 hk', ?_⟩
      rw [← getElem!_pos eu.tabs k hk, eu_get hk'] at he
      rw [unpack_inj' (u_parts.2.2 k hk') (t_parts.2.2.2 i hi) he, Nat.beq_refl]
    · rintro ⟨k, hk, he⟩
      have hk' := List.mem_range.1 hk
      rw [← Nat.eq_of_beq_eq_true he, ← eu_get hk', getElem!_pos eu.tabs k (by rw [eu_size]; exact hk')]
      exact Array.getElem_mem _
  · rw [getElem!_neg _ _ (by simpa [etl_size] using hi)]
    unfold isUT uB vB
    rw [if_neg hi]
    rfl

theorem repArr_eq (i : Nat) : repArr[i]! = repT i := by
  unfold repArr
  by_cases hi : i < 256
  · rw [range_get _ hi, ← bind_parts.2.2.2.1 i hi]
    simp only [mtF_eq, invArr_eq, isUArr_eq]
  · rw [getElem!_neg _ _ (by simpa using hi)]
    unfold repT vB
    rw [if_neg hi]
    rfl

theorem repArr_size : repArr.size = 256 := by simp [repArr]

theorem repsArr_eq : repsArr = [rsT 0, rsT 1, rsT 2, rsT 3].toArray := by
  unfold repsArr
  rw [← bind_parts.2.2.2.2.1]
  simp only [repArr_eq]

theorem repsArr_get (p : Nat) : repsArr[p]! = rsT p := by
  rw [repsArr_eq]
  match p with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | p + 4 =>
    rw [getElem!_neg _ _ (by simp)]
    unfold rsT rsB
    rw [if_neg (by omega)]
    rfl

theorem labArr_eq (i : Nat) : labArr[i]! = labT i := by
  unfold labArr
  by_cases hi : i < 256
  · rw [getElem!_pos _ _ (by simpa [repArr_size] using hi), Array.getElem_map,
      ← getElem!_pos repArr i (by rw [repArr_size]; exact hi), repArr_eq, repsArr_eq,
      List.findIdx?_toArray, bind_parts.2.2.2.2.2 i hi]
  · rw [getElem!_neg _ _ (by simpa [repArr_size] using hi)]
    unfold labT vB
    rw [if_neg hi]
    rfl

theorem labF_eq (i : Nat) : labF i = labT i := labArr_eq i

theorem isUF_eq (i : Nat) : isUF i = isUT i := isUArr_eq i

theorem laddF_eq (p q : Nat) : laddF p q = laddT p q := by
  unfold laddF laddT laddB
  rw [labF_eq, mtF_eq, repsArr_get, repsArr_get]
  rfl

theorem mtF_fun : mtF = mtT := funext fun i => funext fun j => mtF_eq i j
theorem labF_fun : labF = labT := funext labF_eq
theorem isUF_fun : isUF = isUT := funext isUF_eq
theorem laddF_fun : laddF = laddT := funext fun p => funext fun q => laddF_eq p q

theorem fb7_true : fb7Check mtF isUF = true := by
  rw [mtF_fun, isUF_fun]
  exact k_fb7

theorem tables_true : tablesOK = true := by
  have ht := k_tab
  unfold tabK at ht
  unfold tablesOK
  simp only [Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, decide_eq_true_eq, and_assoc] at ht ⊢
  obtain ⟨h8, h11, h12, h13, h14, h15⟩ := ht
  refine ⟨t_parts.2.2.1, etl_size, ?_, eu_size, ?_, mtArr_get.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [u_parts.2.1]
    have hp : ∀ i < UE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false UE.G UE.GI UE.k UE.cnt UE.T
        UE.PL UE.POS UE.SRT UE.SRI i = true := fun i hi =>
      penumSl_spec u_sl i (Nat.zero_le _) (by rw [u_parts.1] at hi; omega) hi
    obtain ⟨a1, -, a3⟩ := (by simpa only [bAnd_iff] using u_hd :
      gensK uGens 42 6 UE.k UE.G = true ∧ Nat.beq UE.cnt 64 = true ∧
        penumHdK (pidn 42 6) UE.cnt 64 UE.T UE.PL = true)
    have hs := penumK_left_sound (cap := 64) (by decide) (gensOK_of a1) a3 hp
    rw [u_parts.1] at hs
    exact hs.2
  · intro k hk
    obtain ⟨i, hi, he⟩ := bind_parts.2.2.1 k hk
    rw [Array.contains_iff_mem, eu_get hk, ← he, ← etl_get hi]
    rw [getElem!_pos _ _ (by rw [etl_size]; exact hi)]
    exact Array.getElem_mem _
  · intro i hi j hj
    obtain ⟨hlt, hmul⟩ := mul_parts hi hj
    rw [mtF_eq, etl_get hlt, etl_get hi, etl_get hj,
      comp_unpack' (t_parts.2.2.2 _ hi) (t_parts.2.2.2 _ hj), hmul]
    exact ⟨hlt, rfl⟩
  · intro i hi
    rw [invArr_eq, mtF_eq]
    exact h8 i hi
  · rw [repsArr_eq]
    rfl
  · simp [labArr, repArr_size]
  · intro i hi
    rw [labF_eq]
    exact h11 i hi
  · intro p hp
    rw [repsArr_get, labF_eq]
    exact h12 p hp
  · rw [labF_eq]
    exact h13
  · intro i hi j hj
    rw [labF_eq, labF_eq, isUF_eq, mtF_eq, invArr_eq]
    exact h14 i hi j hj
  · intro i hi j hj
    rw [labF_eq, labF_eq, labF_eq, mtF_eq, laddF_eq]
    exact h15 i hi j hj

end CertificateChecks.KernelSeitz

end
