module

public import Certificates.Kernel.Sporadic.CF24.Data
public import Certificates.Kernel.Sporadic.OddCore.Suz23000K
public import Certificates.Data.Kernel.Spor.CF24K
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.GSThmBCatalog7CF24
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.CF24

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.CF24 CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelSpor.Suz23000 CFSG.ComponentClassification.GSThmB.CF24

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pv" => pinvS 1782 11 (mask 11)
local notation "wk" => wordK 1782 11 (mask 11) (pidn 1782 11)

@[expose] noncomputable def BF (h : Nat) : Nat := nIf(Nat.beq h 0, B0, B1)

@[expose] noncomputable def BIF (h : Nat) : Nat := nIf(Nat.beq h 0, B0I, B1I)

@[expose] noncomputable def SGF (h : Nat) : Nat := sel7 SG0 SG1 SG2 SG3 SG4 SG5 SG6 h

@[expose] noncomputable def SGIF (h : Nat) : Nat := sel7 SGI0 SGI1 SGI2 SGI3 SGI4 SGI5 SGI6 h

@[expose] noncomputable def LF (j : Nat) : Nat := sel5 L0 L1 L2 L3 L4 j

@[expose] noncomputable def LIF (j : Nat) : Nat := sel5 LI0 LI1 LI2 LI3 LI4 j

theorem permGH : allN 7 (fun k => permB 1782 11 (GH (Nat.succ k))) = true := by
  quickRfl

theorem permB01 : bAnd(permB 1782 11 B0, bAnd(permB 1782 11 B1,
    bAnd(Nat.beq (pv B0) B0I, Nat.beq (pv B1) B1I))) = true := by
  quickRfl

theorem sgK : allN 7 (fun h => Nat.beq (wk BF BIF (nthW IW.W h)) (SGF h)) = true := by
  quickRfl

theorem sgiK : allN 7 (fun h => Nat.beq (pv (SGF h)) (SGIF h)) = true := by
  quickRfl

theorem lK : allN 5 (fun j => Nat.beq (pc (pc (pc (GH 2) (GH (Nat.add j 3))) (pv (GH 2)))
    (pv (GH (Nat.add j 3)))) (LF j)) = true := by
  quickRfl

theorem liK : allN 5 (fun j => Nat.beq (pv (LF j)) (LIF j)) = true := by
  quickRfl

theorem xK : Nat.beq (wk SGF SGIF (codesZ cf24XCodes)) XK = true := by
  quickRfl

theorem yK : Nat.beq (wk SGF SGIF (codesZ cf24YCodes)) YK = true := by
  quickRfl

theorem xyK : bAnd(Nat.beq (wk LF LIF cf24XP) XK, bAnd(Nat.beq (wk LF LIF cf24YP) YK,
    Nat.beq (pc XK YK) (pc YK XK))) = true := by
  quickRfl

theorem omK : Nat.beq (maskL cf24O1) OM = true := by
  quickRfl

theorem oK : allN 5 (fun j => allN 1782 (fun x =>
    Nat.beq (pg 1 (mask 1) OM (pg 11 (mask 11) (LF j) x)) (pg 1 (mask 1) OM x))) = true := by
  quickRfl

theorem bK : allN 5 (fun j => Nat.beq (pc BK (LF j)) (pc (LF j) BK)) = true := by
  quickRfl

theorem ptK : bAnd(Nat.beq (pg 1 (mask 1) OM 6) 1,
    bAnd(Nat.beq (pg 1 (mask 1) OM (pg 11 (mask 11) (SuzTP 0) 6)) 0,
    bAnd(Nat.beq (pg 1 (mask 1) OM (pg 11 (mask 11) BK 6)) 0,
    Nat.beq (pg 1 (mask 1) OM (pg 11 (mask 11) (pc (SuzTP 0) BK) 6)) 0))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.CF24

end
