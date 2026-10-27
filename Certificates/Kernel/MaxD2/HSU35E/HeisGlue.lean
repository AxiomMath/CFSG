module

public import Certificates.Kernel.MaxD2.HSU35E.HeisChecks
public import Certificates.Kernel.MaxD2.HSOver.Glue
public import Certificates.Kernel.MaxD2.HSU.Glue
public import CFSG.Certificates.Kernel.MaxD2.HeisE

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis

@[expose] noncomputable def KEP : Pk where
  n := 100
  w := 7
  kG := 2
  Gp := HSP.GP
  GIp := HSP.GPI
  rcnt := HSU.RE.cnt
  RG := HSU.RE.G
  RGI := HSU.RE.GI
  RT := HSU.RE.T
  RPL := HSU.RE.PL
  RPOS := HSU.RE.POS
  RSRT := HSU.RE.SRT
  RSRI := HSU.RE.SRI
  kN := HSP.NE.k
  cnt := HSP.NE.cnt
  NG := HSP.NE.G
  NGI0 := HSP.NE.GI
  NT := HSP.NE.T
  NPL := HSP.NE.PL
  NPOS := HSP.NE.POS
  NSRT := HSP.NE.SRT
  NSRI := HSP.NE.SRI
  NGI := HSP.NGI
  nr := 0
  REP := fun _ => 0
  REPI := fun _ => 0
  np := 0
  kw := 0
  PT := fun _ => 0
  FS := fun _ => 0
  KS := fun _ => 0
  RB := fun _ => 0
  H := fun _ => 0
  CN := fun _ => 0
  TP := HSP.NE.G 2
  TPI := HSP.NGI 2
  th := r32 MS 0
  CH := CHP
  NH := NHP
  L := fun _ => 0
  hi := 0
  cw := 0
  nl := 0
  MK := fun _ => 0
  mj := 0
  mi := 0

@[expose] noncomputable def KER : Pk where
  n := 100
  w := 7
  kG := 3
  Gp := HSOver.GP
  GIp := HSOver.GPI
  rcnt := HSU.RE.cnt
  RG := HSU.RE.G
  RGI := HSU.RE.GI
  RT := HSU.RE.T
  RPL := HSU.RE.PL
  RPOS := HSU.RE.POS
  RSRT := HSU.RE.SRT
  RSRI := HSU.RE.SRI
  kN := HSOver.NE.k
  cnt := HSOver.NE.cnt
  NG := HSOver.NE.G
  NGI0 := HSOver.NE.GI
  NT := HSOver.NE.T
  NPL := HSOver.NE.PL
  NPOS := HSOver.NE.POS
  NSRT := HSOver.NE.SRT
  NSRI := HSOver.NE.SRI
  NGI := HSOver.NGI
  nr := 0
  REP := fun _ => 0
  REPI := fun _ => 0
  np := 0
  kw := 0
  PT := fun _ => 0
  FS := fun _ => 0
  KS := fun _ => 0
  RB := fun _ => 0
  H := fun _ => 0
  CN := fun _ => 0
  TP := HSOver.NE.G 2
  TPI := HSOver.NGI 2
  th := r32 MS 1
  CH := CHR
  NH := NHR
  L := fun _ => 0
  hi := 0
  cw := 0
  nl := 0
  MK := fun _ => 0
  mj := 0
  mi := 0

theorem comm_all : ∀ k < HSU.RE.cnt, ∀ l < k + 1,
    commK 100 7 HSU.RE.cnt 5 HSU.RE.T (r32 HSU.ZP) (r32 HSU.CZ) k l = true := by
  intro k hk l hl
  have hk' : k < 125 := hk
  by_cases a0 : k < 56
  · exact HSU.comm_of HSU.k_comm0 k (by omega) (by omega) l hl
  by_cases a1 : k < 79
  · exact HSU.comm_of HSU.k_comm1 k (by omega) (by omega) l hl
  by_cases a2 : k < 97
  · exact HSU.comm_of HSU.k_comm2 k (by omega) (by omega) l hl
  by_cases a3 : k < 112
  · exact HSU.comm_of HSU.k_comm3 k (by omega) (by omega) l hl
  · exact HSU.comm_of HSU.k_comm4 k (by omega) (by omega) l hl

theorem hypsEP : HypsHE hsFiveDataP KEP (r32 HSU.ZP) (r32 HSU.ZX) (r32 HSU.CZ) := by
  constructor
  case hn => exact HSP.hypsC.hn
  case hDn => exact rfl
  case hGs => exact rfl
  case hGb => exact HSP.hypsC.hGb
  case hGp => exact HSP.hypsC.hGp
  case hNk => exact rfl
  case hNG => exact HSP.hypsC.hNG
  case hNh => exact HSP.hypsC.hNh
  case hNp => exact HSP.hypsC.hNp
  case hNc => exact rfl
  case hNI => exact HSP.hypsC.hNI
  case hRG =>
    intro j hj
    interval_cases j
    · exact ⟨ch19831_rg0, (PK.allN_iff.1 HSU.k_rgc) 0 (by decide)⟩
    · exact ⟨ch19831_rg1, (PK.allN_iff.1 HSU.k_rgc) 1 (by decide)⟩
  case hRh => exact HSU.k_rh
  case hRp => exact fun i hi => penumSl_spec HSU.k_rsl i (Nat.zero_le _) (by exact hi) hi
  case hRc => exact rfl
  case hNorm =>
    exact fun j hj i hi => band_e ((PK.allN_iff.1 ((PK.allN_iff.1 ch19831_norm) j hj)) i hi)
  case hZ => exact HSU.k_z
  case hUV => exact HSU.k_uv
  case hExp => exact HSU.k_exp
  case hComm => exact comm_all
  case hTw => exact ch19831_tw
  case hTp => exact ch19831_tp
  case hTh => exact Nat.blt_eq.mp ch19831_th1
  case hTn => exact Nat.eq_of_beq_eq_true ch19831_th2
  case hTk => exact ch19831_tk
  case hC => exact fun k hk => (PK.allN_iff.1 ch19831_cent) k hk

theorem hypsER : HypsHE hsFiveDataR KER (r32 HSU.ZP) (r32 HSU.ZX) (r32 HSU.CZ) := by
  constructor
  case hn => exact HSOver.hypsM.hn
  case hDn => exact rfl
  case hGs => exact rfl
  case hGb => exact HSOver.hypsM.hGb
  case hGp => exact HSOver.hypsM.hGp
  case hNk => exact rfl
  case hNG => exact HSOver.hypsM.hNG
  case hNh => exact HSOver.hypsM.hNh
  case hNp => exact HSOver.hypsM.hNp
  case hNc => exact rfl
  case hNI => exact HSOver.hypsM.hNI
  case hRG =>
    intro j hj
    interval_cases j
    · exact ⟨ch19832_rg0, (PK.allN_iff.1 HSU.k_rgc) 0 (by decide)⟩
    · exact ⟨ch19832_rg1, (PK.allN_iff.1 HSU.k_rgc) 1 (by decide)⟩
  case hRh => exact HSU.k_rh
  case hRp => exact fun i hi => penumSl_spec HSU.k_rsl i (Nat.zero_le _) (by exact hi) hi
  case hRc => exact rfl
  case hNorm =>
    exact fun j hj i hi => band_e ((PK.allN_iff.1 ((PK.allN_iff.1 ch19832_norm) j hj)) i hi)
  case hZ => exact HSU.k_z
  case hUV => exact HSU.k_uv
  case hExp => exact HSU.k_exp
  case hComm => exact comm_all
  case hTw => exact ch19832_tw
  case hTp => exact ch19832_tp
  case hTh => exact Nat.blt_eq.mp ch19832_th1
  case hTn => exact Nat.eq_of_beq_eq_true ch19832_th2
  case hTk => exact ch19832_tk
  case hC => exact fun k hk => (PK.allN_iff.1 ch19832_cent) k hk

theorem hsP_heisParts :
    checkInv hsFiveDataP = true ∧ checkHR hsFiveDataP = true ∧ checkN hsFiveDataP = true ∧
      checkHNormal hsFiveDataP = true ∧ checkHZ hsFiveDataP = true ∧
      checkHExp hsFiveDataP = true ∧ checkHComm hsFiveDataP = true ∧
      checkHTorus hsFiveDataP = true ∧ checkHCent hsFiveDataP = true :=
  heisEqParts_of hypsEP

theorem hsR_heisParts :
    checkInv hsFiveDataR = true ∧ checkHR hsFiveDataR = true ∧ checkN hsFiveDataR = true ∧
      checkHNormal hsFiveDataR = true ∧ checkHZ hsFiveDataR = true ∧
      checkHExp hsFiveDataR = true ∧ checkHComm hsFiveDataR = true ∧
      checkHTorus hsFiveDataR = true ∧ checkHCent hsFiveDataR = true :=
  heisEqParts_of hypsER

end CertificateChecks.KernelMaxD2.HSU35E

end
