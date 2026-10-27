module

public import Certificates.Kernel.Sporadic.OddCore.He7200
public import Certificates.Kernel.Sporadic.OddCore.HeL2F

public section

namespace CertificateChecks.KernelSpor.He7200

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.Quasithin.E6.HeInvPerfect
open CertificateChecks.KernelSpor.He2276

theorem commP_eq {a b : Nat} (ha : a < 9) (hb : b < 9) :
    commTab 42 heXTabs[a]! heXTabs[b]! heXInvs[a]! heXInvs[b]! = unpack 42 6 (commP a b) ∧
      canonK 42 6 (mask 6) (42 * 6) (commP a b) = true := by
  obtain ⟨xa, ca⟩ := x_get ha
  obtain ⟨xb, cb⟩ := x_get hb
  have cia := (xp ha).2.2.1
  have cib := (xp hb).2.2.1
  unfold commTab commP
  rw [xa, xb, xi_get ha, xi_get hb, comp42 ca cb, comp42 (canonK_pcomp ca cb) cia,
    comp42 (canonK_pcomp (canonK_pcomp ca cb) cia) cib]
  exact ⟨rfl, canonK_pcomp (canonK_pcomp (canonK_pcomp ca cb) cia) cib⟩

theorem c_ok : GensOK 42 6 HCE.k HCE.G heX1CommGens := by
  obtain ⟨hk, h0, h1⟩ := (by simpa only [bAnd_iff] using c_gens :
    Nat.beq HCE.k 2 = true ∧ Nat.beq (HCE.G 0) (commP 2 8) = true ∧
      Nat.beq (HCE.G 1) (commP 3 8) = true)
  refine ⟨by rw [Nat.eq_of_beq_eq_true hk]; rfl, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true hk] at hj
  match j, hj with
  | 0, _ =>
    rw [Nat.eq_of_beq_eq_true h0]
    exact commP_eq (by decide) (by decide)
  | 1, _ =>
    rw [Nat.eq_of_beq_eq_true h1]
    exact commP_eq (by decide) (by decide)

theorem c_pt {i : Nat} (hi : i < HCE.cnt) : penumPtK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI
    HCE.k HCE.cnt HCE.T HCE.PL HCE.POS HCE.SRT HCE.SRI i = true := by
  have e : HCE.cnt = 10752 := rfl
  rcases Nat.lt_or_ge i 2688 with h0 | h0
  · exact penumSl_spec c_sl0 i (Nat.zero_le _) (by omega) hi
  rcases Nat.lt_or_ge i 5376 with h1 | h1
  · exact penumSl_spec c_sl1 i h0 (by omega) hi
  rcases Nat.lt_or_ge i 8064 with h2 | h2
  · exact penumSl_spec c_sl2 i h1 (by omega) hi
  · exact penumSl_spec c_sl3 i h2 (by omega) hi

theorem c_enum : heX1CommEnum = penumRec 42 6 HCE.cnt HCE.T HCE.PL ∧
    enumOK 42 heX1CommGens (penumRec 42 6 HCE.cnt HCE.T HCE.PL) = true :=
  penumK_left_sound (cap := 10752) idc.2.2 c_ok c_hd (fun _ hi => c_pt hi)

theorem facts7200 : enumOK 42 heX1CommGens heX1CommEnum = true ∧ heX1CommEnum.tabs.size = 10752 := by
  rw [c_enum.1]
  refine ⟨c_enum.2, ?_⟩
  rw [penumRec_eq, Array.size_ofFn]
  rfl

end CertificateChecks.KernelSpor.He7200

end
