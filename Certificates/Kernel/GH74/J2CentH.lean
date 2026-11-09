module

public import Certificates.Kernel.GH74.J2CentG
public import Certificates.Kernel.GH74.Glue
public import CFSG.Certificates.Kernel.Spor.PEnumRSound
public import CFSG.Certificates.Kernel.Spor.PEnumBSound
public import CFSG.Certificates.Kernel.Spor.HKeyUSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2CentE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

theorem pe_of {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat} {gs : Array Table}
    (hg : TabsOK 315 9 k GI gs) (hG : ∀ j < k, G j = pidn 315 9)
    (hh : penumHdK (pidn 315 9) cnt 3000 T PL = true)
    (h : slK cnt (CFSG.KS.PEnumR.penumPtR 315 9 (mask 9) GI k cnt T PL POS SRT SRI) 0 cnt = true) :
    ∀ i < cnt, penumPtK 315 9 (mask 9) (315 * 9) true G GI k cnt T PL POS SRT SRI i = true :=
  CFSG.KS.PEnumR.penumPtK_of_R hn (fun j hj => (hg.2 j hj).2) hG hh
    fun i hi => slK_spec h i (Nat.zero_le _) (by omega) hi

theorem hs_of {cnt : Nat} {T HS HSI : Nat → Nat}
    (h : slK cnt (hsortPtK 315 9 (mask 9) cnt T HS HSI) 0 cnt = true) :
    ∀ i < cnt, hsortPtK 315 9 (mask 9) cnt T HS HSI i = true :=
  fun i hi => slK_spec h i (Nat.zero_le _) (by omega) hi

theorem hsV_of {cnt : Nat} {T HV HS HSI : Nat → Nat}
    (hv : slK cnt (fun i => Nat.beq (hkeyU 315 9 (mask 9) (T i)) (HV i)) 0 cnt = true)
    (h : slK cnt (CFSG.KS.PEnumB.hsortVK cnt HV HS HSI) 0 cnt = true) :
    ∀ i < cnt, hsortPtK 315 9 (mask 9) cnt T HS HSI i = true := by
  refine CFSG.KS.PEnumB.hsortPtK_of_V (HV := HV) (fun i hi => ?_)
    (fun i hi => slK_spec h i (Nat.zero_le _) (by omega) hi)
  have hs := slK_spec hv i (Nat.zero_le _) (by omega) hi
  unfold CFSG.KS.PEnumB.hvK
  rw [← hkeyU_eq]
  exact hs

theorem e_pe : ∀ i < J2E.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2E.G J2E.GI 4 J2E.cnt
    J2E.T J2E.PL J2E.POS J2E.SRT J2E.SRI i = true :=
  pe_of e_tabs (fun j hj => (gens.1 j hj).2.1) sizes.2.2.2.2.2.2.1 eE
theorem e_hs : ∀ i < J2E.cnt, hsortPtK 315 9 (mask 9) J2E.cnt J2E.T J2E.HS J2E.HSI i = true :=
  hs_of eH
theorem o1_pe : ∀ i < J2O1.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2O1.G J2O1.GI 11 J2O1.cnt
    J2O1.T J2O1.PL J2O1.POS J2O1.SRT J2O1.SRI i = true :=
  pe_of o1_tabs (fun j hj => (gens.2.2.2.2.1 j hj).1) sizes.2.2.2.2.2.2.2.1 o1E
theorem o1_hs : ∀ i < J2O1.cnt, hsortPtK 315 9 (mask 9) J2O1.cnt J2O1.T J2O1.HS J2O1.HSI i = true :=
  hs_of o1H
theorem o2_pe : ∀ i < J2O2.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2O2.G J2O2.GI 21 J2O2.cnt
    J2O2.T J2O2.PL J2O2.POS J2O2.SRT J2O2.SRI i = true :=
  pe_of o2_tabs (fun j hj => (gens.2.2.2.2.2.1 j hj).1) sizes.2.2.2.2.2.2.2.2.1 o2E
theorem o2_hs : ∀ i < J2O2.cnt, hsortPtK 315 9 (mask 9) J2O2.cnt J2O2.T J2O2.HS J2O2.HSI i = true :=
  hs_of o2H
theorem s1_pe : ∀ i < J2S1.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2S1.G J2S1.GI 6 J2S1.cnt
    J2S1.T J2S1.PL J2S1.POS J2S1.SRT J2S1.SRI i = true :=
  pe_of s1_tabs (fun j hj => (gens.2.2.2.2.2.2.2.2.1 j hj).2.1) sizes.2.2.2.2.2.2.2.2.2.2.1 s1E
theorem s1_hs : ∀ i < J2S1.cnt, hsortPtK 315 9 (mask 9) J2S1.cnt J2S1.T J2S1.HS J2S1.HSI i = true :=
  hsV_of s1H s1Hs
theorem s2_pe : ∀ i < J2S2.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2S2.G J2S2.GI 6 J2S2.cnt
    J2S2.T J2S2.PL J2S2.POS J2S2.SRT J2S2.SRI i = true :=
  pe_of s2_tabs (fun j hj => (gens.2.2.2.2.2.2.2.2.2 j hj).2.1) sizes.2.2.2.2.2.2.2.2.2.2.2 s2E
theorem s2_hs : ∀ i < J2S2.cnt, hsortPtK 315 9 (mask 9) J2S2.cnt J2S2.T J2S2.HS J2S2.HSI i = true :=
  hsV_of s2H s2Hs

theorem pf_pe : ∀ i < J2PF.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2PF.G J2PF.GI 3 J2PF.cnt
    J2PF.T J2PF.PL J2PF.POS J2PF.SRT J2PF.SRI i = true := by
  have hc : J2PF.cnt = 1920 := sizes.2.2.2.1
  refine CFSG.KS.PEnumR.penumPtK_of_R hn (fun j hj => (pf_tabs.2 j hj).2)
    (fun j hj => (gens.2.2.2.2.2.2.2.1 j hj).1) sizes.2.2.2.2.2.2.2.2.2.1 fun i hi => ?_
  have h8 : i / 240 < 8 := by omega
  have hs := pfE_all (i / 240) h8
  exact slK_spec hs i (by change 240 * (i / 240) ≤ i; omega)
    (by change i < 240 * (i / 240) + 240; omega) hi

theorem pf_hs : ∀ i < J2PF.cnt, hsortPtK 315 9 (mask 9) J2PF.cnt J2PF.T J2PF.HS J2PF.HSI i = true := by
  have hc : J2PF.cnt = 1920 := sizes.2.2.2.1
  refine CFSG.KS.PEnumB.hsortPtK_of_V (HV := J2PFV) (fun i hi => ?_)
    (fun i hi => slK_spec pfHs i (Nat.zero_le _) (by omega) hi)
  have h8 : i / 240 < 8 := by omega
  have hs := slK_spec (pfH_all (i / 240) h8) i (by change 240 * (i / 240) ≤ i; omega)
    (by change i < 240 * (i / 240) + 240; omega) hi
  unfold CFSG.KS.PEnumB.hvK
  rw [← hkeyU_eq]
  exact hs

theorem e_invs : ∀ j < 4, invEqK 315 9 (mask 9) (315 * 9) (J2E.GI j) (J2EI j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2EI j) = true :=
  fun j hj => ⟨(gens.1 j hj).2.2.2, (gens.1 j hj).2.2.1⟩

theorem o1_invs : ∀ j < 11, invEqK 315 9 (mask 9) (315 * 9) (J2O1.GI j) (J2O1I j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2O1I j) = true :=
  fun j hj => ⟨(gens.2.2.2.2.1 j hj).2.2, (gens.2.2.2.2.1 j hj).2.1⟩

theorem o2_invs : ∀ j < 21, invEqK 315 9 (mask 9) (315 * 9) (J2O2.GI j) (J2O2I j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2O2I j) = true :=
  fun j hj => ⟨(gens.2.2.2.2.2.1 j hj).2.2, (gens.2.2.2.2.2.1 j hj).2.1⟩

theorem pf_invs : ∀ j < 3, invEqK 315 9 (mask 9) (315 * 9) (J2PF.GI j) (J2PFI j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2PFI j) = true :=
  fun j hj => ⟨(gens.2.2.2.2.2.2.2.1 j hj).2.2, (gens.2.2.2.2.2.2.2.1 j hj).2.1⟩

theorem s1_invs : ∀ j < 6, invEqK 315 9 (mask 9) (315 * 9) (J2S1.GI j) (J2S1I j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2S1I j) = true :=
  fun j hj => ⟨(gens.2.2.2.2.2.2.2.2.1 j hj).2.2.2, (gens.2.2.2.2.2.2.2.2.1 j hj).2.2.1⟩

theorem s2_invs : ∀ j < 6, invEqK 315 9 (mask 9) (315 * 9) (J2S2.GI j) (J2S2I j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2S2I j) = true :=
  fun j hj => ⟨(gens.2.2.2.2.2.2.2.2.2 j hj).2.2.2, (gens.2.2.2.2.2.2.2.2.2 j hj).2.2.1⟩

theorem e_enum : enumOK 315 cap j2EGens 32 = true :=
  evEnum_of_pos hn (fun j hj => (gens.1 j hj).2.1) e_tabs e_invs sizes.2.2.2.2.2.2.1 e_pe e_hs
    sizes.1

theorem o1_enum : enumOK 315 cap (j2TA :: conjOrbit j2Orb1Root j2Orb1Conj) 32 = true :=
  evEnum_of_pos hn (fun j hj => (gens.2.2.2.2.1 j hj).1) o1_tabs o1_invs sizes.2.2.2.2.2.2.2.1 o1_pe
    o1_hs sizes.2.1

theorem o2_enum : enumOK 315 cap (j2TA :: conjOrbit j2Orb2Root j2Orb2Conj) 32 = true :=
  evEnum_of_pos hn (fun j hj => (gens.2.2.2.2.2.1 j hj).1) o2_tabs o2_invs sizes.2.2.2.2.2.2.2.2.1
    o2_pe o2_hs sizes.2.2.1

theorem pf_enum : enumOK 315 cap j2PerfComm 1920 = true :=
  evEnum_of_pos hn (fun j hj => (gens.2.2.2.2.2.2.2.1 j hj).1) pf_tabs pf_invs
    sizes.2.2.2.2.2.2.2.2.2.1 pf_pe pf_hs sizes.2.2.2.1

theorem s1_enum : enumOK 315 cap j2S1Gens 128 = true :=
  evEnum_of_pos hn (fun j hj => (gens.2.2.2.2.2.2.2.2.1 j hj).2.1) s1_tabs s1_invs
    sizes.2.2.2.2.2.2.2.2.2.2.1 s1_pe s1_hs sizes.2.2.2.2.1

theorem s2_enum : enumOK 315 cap j2S2Gens 128 = true :=
  evEnum_of_pos hn (fun j hj => (gens.2.2.2.2.2.2.2.2.2 j hj).2.1) s2_tabs s2_invs
    sizes.2.2.2.2.2.2.2.2.2.2.2 s2_pe s2_hs sizes.2.2.2.2.2.1

theorem e_arr : j2E = (hRec 315 9 J2E.cnt J2E.T J2E.PL).1 :=
  closArr_eq (cap := cap) hn (fun j hj => (gens.1 j hj).2.1) e_tabs sizes.2.2.2.2.2.2.1 e_pe e_hs

theorem s1_arr : closArr 315 cap j2S1Gens = (hRec 315 9 J2S1.cnt J2S1.T J2S1.PL).1 :=
  closArr_eq (cap := cap) hn (fun j hj => (gens.2.2.2.2.2.2.2.2.1 j hj).2.1) s1_tabs
    sizes.2.2.2.2.2.2.2.2.2.2.1 s1_pe s1_hs

theorem s2_arr : closArr 315 cap j2S2Gens = (hRec 315 9 J2S2.cnt J2S2.T J2S2.PL).1 :=
  closArr_eq (cap := cap) hn (fun j hj => (gens.2.2.2.2.2.2.2.2.2 j hj).2.1) s2_tabs
    sizes.2.2.2.2.2.2.2.2.2.2.2 s2_pe s2_hs

theorem eT {i : Nat} (hi : i < J2E.cnt) : canonK 315 9 (mask 9) (315 * 9) (J2E.T i) = true :=
  penumPt_canon (e_pe i hi)

theorem s1T {i : Nat} (hi : i < J2S1.cnt) : canonK 315 9 (mask 9) (315 * 9) (J2S1.T i) = true :=
  penumPt_canon (s1_pe i hi)

theorem s2T {i : Nat} (hi : i < J2S2.cnt) : canonK 315 9 (mask 9) (315 * 9) (J2S2.T i) = true :=
  penumPt_canon (s2_pe i hi)

end CertificateChecks.KernelGH74.J2CentE

end
