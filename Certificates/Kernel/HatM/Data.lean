module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatMInputs
public import Certificates.Data.Kernel.HatChkK
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatMInputs
public meta import Certificates.Data.Kernel.HatChkK
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHatM

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Quasithin.H13.Ch4.HatChk CFSG.Quasithin.H13.Ch4.HatM CFSG.KC.HatChkK
open CFSG.Sporadic.Mathieu

meta def repArrs : Array (Array Nat) := #[r1Arr, r2Arr, cArr]

meta def abArrs : Array (Array Nat) := #[arr24 m24gA, arr24 m24gB]

meta def abiArrs : Array (Array Nat) := #[arr24 m24gA⁻¹, arr24 m24gB⁻¹]

meta def clsArrs : Array (Array Nat) := #[clsP]

end CertificateChecks.KernelHatM

end

#kb3_enum CertificateChecks.KernelHatM.ES1 CFSG.Quasithin.H13.Ch4.HatM.s1Gens
  CFSG.KC.HatChkK.base24 24 5
#kb3_enum CertificateChecks.KernelHatM.EP1 CFSG.Quasithin.H13.Ch4.HatM.p1Gens
  CFSG.KC.HatChkK.base24 24 5
#kb3_enum CertificateChecks.KernelHatM.EP2 CFSG.Quasithin.H13.Ch4.HatM.p2Gens
  CFSG.KC.HatChkK.base24 24 5
#kmisc_packarrs CertificateChecks.KernelHatM.RA CertificateChecks.KernelHatM.repArrs 5
#kmisc_packarrs CertificateChecks.KernelHatM.AB CertificateChecks.KernelHatM.abArrs 5
#kmisc_packarrs CertificateChecks.KernelHatM.ABI CertificateChecks.KernelHatM.abiArrs 5
#kmisc_packarrs CertificateChecks.KernelHatM.CL CertificateChecks.KernelHatM.clsArrs 6

public section

namespace CertificateChecks.KernelHatM

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Quasithin.H13.Ch4.HatChk CFSG.Quasithin.H13.Ch4.HatM CFSG.KC.HatChkK
open CFSG.Sporadic.Mathieu
open CFSG.KC.Enum (pg pcomp pidn permOK)
open CFSG.KS (mask pinvS)
open CFSG.KC.Misc.ArrEnum (permB arrBind)

@[expose] noncomputable def memP (i : ℕ) : Bool :=
  (List.range 1024).any fun j => Nat.beq (EP1.T i) (EP2.T j)

@[expose] noncomputable def memI (i : ℕ) : Bool :=
  if i < 1024 then memP i else CFSG.KC.HatChkK.memL 24 ps24 cP2.pts cP1.pts[i]!

@[expose] noncomputable def memC (i : ℕ) : Bool := if i < 1024 then memP i else false

@[expose] noncomputable def cmI (i j : ℕ) : Bool :=
  if i < 1024 ∧ j < 1024 then cmK 24 5 (EP1.T i) (EP1.T j) else cmA 24 cP1.pts[i]! cP1.pts[j]!

@[expose] noncomputable def clsC (i : ℕ) : ℕ := if i < 1024 then pg 6 (mask 6) (CL 0) i else 0

theorem sz5 : CFSG.KS.Raw.szOK 24 5 = true := by quickRfl

theorem nS1 : s1Gens.size = 9 := by decide +kernel

theorem nP1 : p1Gens.size = 10 := by decide +kernel

theorem nP2 : p2Gens.size = 10 := by decide +kernel

theorem nums : ES1.ng = 9 ∧ EP1.ng = 10 ∧ EP2.ng = 10 ∧ ES1.N = 512 ∧ EP1.N = 1024 ∧
    EP2.N = 1024 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bR1 : arrBind r1Arr 24 5 (RA 0) = true := by quickRfl

theorem bR2 : arrBind r2Arr 24 5 (RA 1) = true := by quickRfl

theorem bA : arrBind (arr24 m24gA) 24 5 (AB 0) = true := by quickRfl

theorem bB : arrBind (arr24 m24gB) 24 5 (AB 1) = true := by quickRfl

theorem bId : arrBind (arr24 1) 24 5 (pidn 24 5) = true := by quickRfl

theorem pAB : (List.range 2).all (fun k => permOK 24 5 (mask 5) (24 * 5) (AB k) (ABI k)) = true := by
  quickRfl

theorem pS1 : (List.range 9).all (fun k => permB 24 5 (ES1.G k)) = true := by quickRfl

theorem pP1 : (List.range 10).all (fun k => permB 24 5 (EP1.G k)) = true := by quickRfl

theorem pP2 : (List.range 10).all (fun k => permB 24 5 (EP2.G k)) = true := by quickRfl

theorem pR : (List.range 3).all (fun k => permB 24 5 (RA k)) = true := by quickRfl

theorem fpfR1 : fpfK 24 5 (RA 0) = true := by quickRfl

theorem cmS1 : (List.range 9).all (fun k => cmK 24 5 (ES1.G k) (RA 0)) = true := by quickRfl

theorem cmC : cmK 24 5 (RA 2) (RA 1) = true := by quickRfl

theorem cmP1 : (List.range 10).all (fun k => cmK 24 5 (EP1.G k) (RA 1)) = true := by quickRfl

theorem conjP2 : (List.range 10).all (fun k => Nat.beq (EP2.G k)
    (pcomp 24 5 (mask 5) (RA 2) (pcomp 24 5 (mask 5) (EP1.G k) (pinvS 24 5 (mask 5) (RA 2))))) =
      true := by
  quickRfl

end CertificateChecks.KernelHatM

end
