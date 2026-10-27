
module

public import Certificates.Kernel.Sporadic.OddCore.ON2129
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.ON2129

open CFSG.ONSchreier CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native

theorem szOK32 : szOK 32 6 = true := by
  quickRfl

theorem t32_pt {i : Nat} (hi : i < T32E.cnt) : penumPtK 32 6 (mask 6) (32 * 6) false T32E.G
    T32E.GI T32E.k T32E.cnt T32E.T T32E.PL T32E.POS T32E.SRT T32E.SRI i = true := by
  have e : T32E.cnt = 512 := rfl
  exact penumSl_spec t32_sl i (Nat.zero_le _) (by omega) hi

theorem sq_pt {i : Nat} (hi : i < SQE.cnt) : penumPtK 32 6 (mask 6) (32 * 6) false SQE.G
    SQE.GI SQE.k SQE.cnt SQE.T SQE.PL SQE.POS SQE.SRT SQE.SRI i = true := by
  have e : SQE.cnt = 64 := rfl
  exact penumSl_spec sq_sl i (Nat.zero_le _) (by omega) hi

theorem om_pt {i : Nat} (hi : i < OME.cnt) : penumPtK 32 6 (mask 6) (32 * 6) false OME.G
    OME.GI OME.k OME.cnt OME.T OME.PL OME.POS OME.SRT OME.SRI i = true := by
  have e : OME.cnt = 8 := rfl
  exact penumSl_spec om_sl i (Nat.zero_le _) (by omega) hi

theorem t32Enum_eq : t32Enum = penumRec 32 6 T32E.cnt T32E.T T32E.PL :=
  (penumK_left_sound (cap := 600) szOK32 (gensOK_of t32_gens) t32_hd (fun _ hi => t32_pt hi)).1

theorem idCanon : canonK 32 6 (mask 6) (32 * 6) (pidn 32 6) = true ∧ idK 32 6 (mask 6) = true := by
  obtain ⟨-, -, h1, h2⟩ := (by simpa only [bAnd_iff] using om_facts :
    allN 8 (fun a => allN 8 (fun b => Nat.beq (pcomp 32 6 (mask 6) (OME.T a) (OME.T b))
      (pcomp 32 6 (mask 6) (OME.T b) (OME.T a)))) = true ∧
    allN 8 (fun a => Nat.beq (pcomp 32 6 (mask 6) (OME.T a) (OME.T a)) (pidn 32 6)) = true ∧
    canonK 32 6 (mask 6) (32 * 6) (pidn 32 6) = true ∧ idK 32 6 (mask 6) = true)
  exact ⟨h1, h2⟩

theorem idTab_eq : idTab 32 = unpack 32 6 (pidn 32 6) := (idK_sound idCanon.2).symm

theorem comp_unpack {p q : Nat} (hp : canonK 32 6 (mask 6) (32 * 6) p = true)
    (hq : canonK 32 6 (mask 6) (32 * 6) q = true) :
    comp 32 (unpack 32 6 p) (unpack 32 6 q) = unpack 32 6 (pcomp 32 6 (mask 6) p q) :=
  compA_unpack hp hq

theorem rec_get {cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (penumRec 32 6 cnt T PL).tabs[i]! = unpack 32 6 (T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem sq_gensOK : GensOK 32 6 SQE.k SQE.G sqTabs := by
  refine ⟨?_, fun j hj => ⟨?_, ((bAnd_iff _ _).1 (allN_spec sq_gens j hj)).2⟩⟩
  · rw [sqTabs, t32Enum_eq]
    simp [penumRec]
    rfl
  · have hj' : j < T32E.cnt := hj
    have hc := penumPt_canon (t32_pt hj')
    have he := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec sq_gens j hj)).1
    rw [sqTabs, t32Enum_eq, getElem!_pos _ j (by simp [penumRec]; exact hj'), Array.getElem_map,
      ← getElem!_pos _ j (by simp [penumRec]; exact hj'), rec_get hj', comp_unpack hc hc, he]

theorem sqEnum_eq : sqEnum = penumRec 32 6 SQE.cnt SQE.T SQE.PL ∧
    enumOK 32 sqTabs (penumRec 32 6 SQE.cnt SQE.T SQE.PL) = true :=
  penumK_left_sound (cap := 200) szOK32 sq_gensOK sq_hd (fun _ hi => sq_pt hi)

theorem omegaTabs_eq : omegaTabs = (omSel.map fun i => unpack 32 6 (SQE.T i)).toArray := by
  rw [omegaTabs, sqEnum_eq.1]
  simp only [penumRec]
  refine (filter_ofFn (m := SQE.cnt) (f := fun i => unpack 32 6 (SQE.T i)) _).trans ?_
  refine congrArg (fun l : List Nat => (l.map fun i => unpack 32 6 (SQE.T i)).toArray) ?_
  refine Eq.trans ?_ (sel_spec om_sel)
  apply List.filter_congr
  intro i hi
  have hi' : i < SQE.cnt := List.mem_range.1 hi
  have hc := penumPt_canon (sq_pt hi')
  rw [comp_unpack hc hc, idTab_eq, beq_unpack (canonK_pcomp hc hc) idCanon.1]

theorem om_gensOK : GensOK 32 6 OME.k OME.G omegaTabs := by
  rw [omegaTabs_eq]
  refine ⟨?_, fun j hj => ⟨?_, ((bAnd_iff _ _).1 (allN_spec om_gens j hj)).2⟩⟩
  · simp only [List.size_toArray, List.length_map]
    rfl
  · have hl : j < omSel.length := hj
    have he := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec om_gens j hj)).1
    rw [getElem!_pos _ j (by simpa using hl), List.getElem_toArray, List.getElem_map, he,
      nget_get omSel hl]

theorem omegaEnum_eq : omegaEnum = penumRec 32 6 OME.cnt OME.T OME.PL ∧
    enumOK 32 omegaTabs (penumRec 32 6 OME.cnt OME.T OME.PL) = true :=
  penumK_left_sound (cap := 20) szOK32 om_gensOK om_hd (fun _ hi => om_pt hi)

theorem facts2129 : enumOK 32 sqTabs sqEnum = true ∧ sqEnum.tabs.size = 64 ∧
    enumOK 32 omegaTabs omegaEnum = true ∧ omegaEnum.tabs.size = 8 ∧
    omegaEnum.tabs.all (fun a => omegaEnum.tabs.all fun b => comp 32 a b == comp 32 b a) =
      true ∧
    omegaEnum.tabs.all (fun a => comp 32 a a == idTab 32) = true := by
  obtain ⟨hcomm, hsq, -, -⟩ := (by simpa only [bAnd_iff] using om_facts :
    allN 8 (fun a => allN 8 (fun b => Nat.beq (pcomp 32 6 (mask 6) (OME.T a) (OME.T b))
      (pcomp 32 6 (mask 6) (OME.T b) (OME.T a)))) = true ∧
    allN 8 (fun a => Nat.beq (pcomp 32 6 (mask 6) (OME.T a) (OME.T a)) (pidn 32 6)) = true ∧
    canonK 32 6 (mask 6) (32 * 6) (pidn 32 6) = true ∧ idK 32 6 (mask 6) = true)
  rw [sqEnum_eq.1, omegaEnum_eq.1]
  refine ⟨sqEnum_eq.2, by simp [penumRec]; rfl, omegaEnum_eq.2, by simp [penumRec]; rfl, ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro a ha
    rw [Array.all_eq_true]
    intro b hb
    have ha' : a < OME.cnt := by simpa [penumRec] using ha
    have hb' : b < OME.cnt := by simpa [penumRec] using hb
    have hca := penumPt_canon (om_pt ha')
    have hcb := penumPt_canon (om_pt hb')
    simp only [penumRec, Array.getElem_ofFn]
    rw [comp_unpack hca hcb, comp_unpack hcb hca,
      beq_unpack (canonK_pcomp hca hcb) (canonK_pcomp hcb hca)]
    exact allN_spec (allN_spec hcomm a ha') b hb'
  · rw [Array.all_eq_true]
    intro a ha
    have ha' : a < OME.cnt := by simpa [penumRec] using ha
    have hca := penumPt_canon (om_pt ha')
    simp only [penumRec, Array.getElem_ofFn]
    rw [comp_unpack hca hca, idTab_eq, beq_unpack (canonK_pcomp hca hca) idCanon.1]
    exact allN_spec hsq a ha'

end CertificateChecks.KernelSpor.ON2129

end
