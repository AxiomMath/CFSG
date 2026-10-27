module

public import Certificates.Kernel.SporSch.Ru.C2248
public import Certificates.Kernel.SporSch.Ru.C2253
public meta import CFSG.Quasithin.H13.L32ARuU1Inputs
import all Init.Data.Nat.Fold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.H13.L32ARuU1Inputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuU1

open CFSG.Quasithin.H13.KGRu

meta def uaM : Array (Array Nat) := ruU1Arr
meta def ufM : Array (Array Nat) := ruU1FArr
meta def bwM : Array (Array Nat) := (Array.range 4).map ruU1BasisA
meta def oaM : Array (Array Nat) := (Array.range 6).map fun k => ruCW (ruOddA k)
meta def obM : Array (Array Nat) := (Array.range 6).map fun k => ruCW (ruOddB k)

end CertificateChecks.KernelSporSch.RuU1

#kss_perms CertificateChecks.KernelSporSch.RuU1.UA 12 CertificateChecks.KernelSporSch.RuU1.uaM
#kss_perms CertificateChecks.KernelSporSch.RuU1.UF 11 CertificateChecks.KernelSporSch.RuU1.ufM
#kss_perms CertificateChecks.KernelSporSch.RuU1.BW 12 CertificateChecks.KernelSporSch.RuU1.bwM
#kss_perms CertificateChecks.KernelSporSch.RuU1.OA 12 CertificateChecks.KernelSporSch.RuU1.oaM
#kss_perms CertificateChecks.KernelSporSch.RuU1.OB 12 CertificateChecks.KernelSporSch.RuU1.obM

namespace CertificateChecks.KernelSporSch.RuU1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.H13.KGRu CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuB1K
  CertificateChecks.KernelSporSch.RuLines CertificateChecks.KernelSporSch.RuCe

@[expose] noncomputable def lgN (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) i) l

@[expose] noncomputable def lgL (l : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun j _ => ih j) i) l

@[expose] noncomputable def pw (X e : Nat) : Nat := ppow 4060 12 (mask 12) (pidn 4060 12) X e

@[expose] noncomputable def cn (X : Nat) : Bool := canonK 4060 12 (mask 12) (4060 * 12) X

@[expose] noncomputable def xK (i : Nat) : Nat :=
  pc (pw Z (Nat.mod i 2)) (pc (pw (BW 0) (Nat.mod (Nat.div i 2) 2))
    (pc (pw (BW 1) (Nat.mod (Nat.div i 4) 2))
      (pc (pw (BW 2) (Nat.mod (Nat.div i 8) 2)) (pw (BW 3) (Nat.mod (Nat.div i 16) 2)))))

@[expose] noncomputable def mulRow (i : Nat) : Bool :=
  allN 32 (fun j => bAnd(Nat.blt (Nat.xor i j) 32, Nat.beq (pc (UA i) (UA j)) (UA (Nat.xor i j))))

end CertificateChecks.KernelSporSch.RuU1

#kss_each CertificateChecks.KernelSporSch.RuU1.ch7152m CertificateChecks.KernelSporSch.RuU1.mulRow 32

namespace CertificateChecks.KernelSporSch.RuU1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.H13.KGRu CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuB1K
  CertificateChecks.KernelSporSch.RuLines CertificateChecks.KernelSporSch.RuCe

theorem ch7152wB : allN 4 (fun k => bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 C0 C1)
    (gen2 C0I C1I) 2 (dword ruU1Words 0 k) (BW k), cn (BW k))) = true := by quickRfl
theorem ch7152wA : allN 6 (fun k => bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 C0 C1)
    (gen2 C0I C1I) 2 (ruOddA k) (OA k), cn (OA k))) = true := by quickRfl
theorem ch7152wO : allN 6 (fun k => bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 C0 C1)
    (gen2 C0I C1I) 2 (ruOddB k) (OB k), cn (OB k))) = true := by quickRfl
theorem ch7152pw : allN 2 (fun e => bAnd(cn (pw Z e), allN 4 (fun k => cn (pw (BW k) e)))) = true := by
  quickRfl
theorem ch7152x : allN 32 (fun i => bAnd(Nat.beq (xK i) (UA i), cn (UA i))) = true := by quickRfl
theorem ch7152f : allN 32 (fun i => bAnd(resK 1920 12 11 RuF.F RuF.FPOS (UA i) (UF i),
    canonK 1920 11 (mask 11) (1920 * 11) (UF i))) = true := by quickRfl
theorem ch7152ne : allN 32 (fun i => bIf(Nat.beq i 0, true, !Nat.beq (UA i) (pidn 4060 12))) = true := by
  quickRfl
theorem ch7152cs : allN 4 (fun k => cn (SGI k)) = true := by quickRfl
theorem ch7152t3 : allN 4 (fun k => allN 32 (fun i => bAnd(Nat.blt (lgN (lgL ruU1Sig k) i) 32,
    Nat.beq (pc (pc (SG k) (UA i)) (SGI k)) (UA (lgN (lgL ruU1Sig k) i))))) = true := by quickRfl
theorem ch7152t4 : allN 7 (fun m => bAnd(Nat.blt (lgN ruU1Tau m) 32,
    Nat.beq (EA m) (UA (lgN ruU1Tau m)))) = true := by quickRfl
theorem ch7152pair : allN 32 (fun a => allN 32 (fun b => ruU1PairOK a b)) = true := by quickRfl
theorem ch7152n : allN 2 (fun k => allN 7 (fun m => bAnd(Nat.blt (lgN (lgL ruEPi k) m) 7,
    Nat.beq (CFSG.KS.SporSch.conjP (gen2 Ns0 Ns1 k) (gen2 Ns0I Ns1I k) (EA m))
      (EA (lgN (lgL ruEPi k) m))))) = true := by quickRfl
theorem ch7152c : Nat.beq (pc (pc (pc (SG 0) (EA 2)) (SGI 0)) (EA 2)) Z = true := by quickRfl
theorem ch7152o : allN 6 (fun k => bAnd(Nat.beq (pw (pc (pc (JG k) (OA k)) (OB k)) (ruOddM k))
    (pidn 4060 12), bAnd(Nat.beq (pw (OA k) (ruOddMA k)) (pidn 4060 12),
      Nat.beq (pw (OB k) (ruOddMB k)) (pidn 4060 12)))) = true := by quickRfl

theorem ch7152neg1 : (!Nat.beq (pc (UA 1) (UA 2)) (UA 2)) = true := by quickRfl
theorem ch7152neg2 : (!Nat.beq (pc (pc (SG 2) (UA 2)) (SGI 2)) (UA 2)) = true := by quickRfl
theorem ch7152neg3 : (!Nat.beq (xK 3) (UA 2)) = true := by quickRfl
theorem ch7152neg4 : (!Nat.beq (pw (OA 0) 2) (pidn 4060 12)) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuU1

end
