module

public import Certificates.Kernel.SporSch.Ly.SylTab
public import CFSG.Sporadic.Schreier.LyCheckSylow
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySt

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySyl
open CFSG.Sporadic.LySchreier.Native

@[expose] noncomputable def getL (L : List (List Nat)) (t : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun i' _ => ih i') i) L t

@[expose] noncomputable def lenLL (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ acc => Nat.succ acc) L

@[expose] noncomputable def allLL (n : Nat) (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun E _ acc => bAnd(incL E, bAnd(CFSG.KS.Mathieu.allLtN n E, acc))) L

theorem plAll : allN 256 (fun j => plOK LySy.W PL 256 j) = true := by quickRfl
theorem pl0 : Nat.beq (PL 0) 0 = true := by quickRfl

@[expose] noncomputable def rowQ (i : Nat) : Bool := rowOK MT LySy.W PL 256 i

@[expose] noncomputable def chkQ (i : Nat) : Bool := rowChk MT IV 256 (dMask DT nD) i

@[expose] noncomputable def cmQ (s : Nat) : Bool :=
  Nat.beq (commsK MT IV 256 CM 4096 (Nat.mul s 4096) (Nat.land (ST s) 65535)
    (Nat.shiftRight (ST s) 16)) (ST (Nat.succ s))

@[expose] noncomputable def eaQ (L : List (List Nat)) (NM CT : Nat → Nat) (nN t : Nat) : Bool :=
  bIf(Nat.blt t (lenLL L), Nat.beq (eaOne MT NM 256 nN (maskL (getL L t)) (lenL (getL L t)) (CT t))
    (CT (Nat.succ t)), true)

@[expose] noncomputable def nmQ (L : List (List Nat)) (NM : Nat → Nat) (nN j : Nat) : Bool :=
  bIf(Nat.blt j nN, listOfM (NM j) 256 (getL L j), true)

@[expose] noncomputable def ea1Q (t : Nat) : Bool := eaQ [[0]] NM1 CT1 nN1 t
@[expose] noncomputable def ea2Q (t : Nat) : Bool := eaQ L1 NM2 CT2 nN2 t
@[expose] noncomputable def ea3Q (t : Nat) : Bool := eaQ L2 NM3 CT3 nN3 t
@[expose] noncomputable def ea4Q (t : Nat) : Bool := eaQ L3 NM4 CT4 nN4 t
@[expose] noncomputable def nm1Q (j : Nat) : Bool := nmQ L1 NM1 nN1 j
@[expose] noncomputable def nm2Q (j : Nat) : Bool := nmQ L2 NM2 nN2 j
@[expose] noncomputable def nm3Q (j : Nat) : Bool := nmQ L3 NM3 nN3 j
@[expose] noncomputable def nm4Q (j : Nat) : Bool := nmQ L4 NM4 nN4 j

end CertificateChecks.KernelSporSch.LySt

#kly_chain CertificateChecks.KernelSporSch.LySt row CertificateChecks.KernelSporSch.LySt.rowQ 32 8
#kly_chain CertificateChecks.KernelSporSch.LySt chk CertificateChecks.KernelSporSch.LySt.chkQ 32 8
#kly_chain CertificateChecks.KernelSporSch.LySt cm CertificateChecks.KernelSporSch.LySt.cmQ 1 16
#kly_chain CertificateChecks.KernelSporSch.LySt ea1 CertificateChecks.KernelSporSch.LySt.ea1Q 1 1
#kly_chain CertificateChecks.KernelSporSch.LySt ea2 CertificateChecks.KernelSporSch.LySt.ea2Q 64 4
#kly_chain CertificateChecks.KernelSporSch.LySt ea3 CertificateChecks.KernelSporSch.LySt.ea3Q 64 4
#kly_chain CertificateChecks.KernelSporSch.LySt ea4 CertificateChecks.KernelSporSch.LySt.ea4Q 64 4
#kly_chain CertificateChecks.KernelSporSch.LySt nm1 CertificateChecks.KernelSporSch.LySt.nm1Q 64 4
#kly_chain CertificateChecks.KernelSporSch.LySt nm2 CertificateChecks.KernelSporSch.LySt.nm2Q 64 4
#kly_chain CertificateChecks.KernelSporSch.LySt nm3 CertificateChecks.KernelSporSch.LySt.nm3Q 64 4
#kly_chain CertificateChecks.KernelSporSch.LySt nm4 CertificateChecks.KernelSporSch.LySt.nm4Q 64 4

namespace CertificateChecks.KernelSporSch.LySt

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySyl
open CFSG.Sporadic.LySchreier.Native

theorem dtOK : Nat.beq (dtRun MT CM DT nC nD) nD = true := by quickRfl
theorem dCk : dChk MT IV 256 DT nD = true := by quickRfl
theorem e0 : eChk MT 256 (L4.getD 0 []) = true := by quickRfl
theorem e1 : eChk MT 256 (L4.getD 1 []) = true := by quickRfl
theorem q : qChk MT IV 256 qIndices.toList (L4.getD 0 []) (L4.getD 1 []) (fIndex ()) = true := by
  quickRfl
theorem st0 : Nat.beq (ST 0) 0 = true := by quickRfl
theorem nCk : Nat.beq (Nat.land (ST 16) 65535) nC = true := by quickRfl
theorem nClt : Nat.blt nC 65535 = true := by quickRfl
theorem l0 : allLL 256 [[0]] = true := by quickRfl
theorem l1 : allLL 256 L1 = true := by quickRfl
theorem l2 : allLL 256 L2 = true := by quickRfl
theorem l3 : allLL 256 L3 = true := by quickRfl
theorem ct : bAnd(Nat.beq (CT1 0) 0, bAnd(Nat.beq (CT2 0) 0, bAnd(Nat.beq (CT3 0) 0,
    Nat.beq (CT4 0) 0))) = true := by quickRfl
theorem ctN : bAnd(Nat.beq (CT1 1) nN1, bAnd(Nat.beq (CT2 (lenLL L1)) nN2,
    bAnd(Nat.beq (CT3 (lenLL L2)) nN3, Nat.beq (CT4 (lenLL L3)) nN4))) = true := by quickRfl
theorem lens : bAnd(Nat.beq (lenLL L1) nN1, bAnd(Nat.beq (lenLL L2) nN2, bAnd(Nat.beq (lenLL L3) nN3,
    bAnd(Nat.beq (lenLL L4) nN4, bAnd(Nat.ble (lenLL L1) 256, bAnd(Nat.ble (lenLL L2) 256,
    bAnd(Nat.ble (lenLL L3) 256, bAnd(Nat.ble (lenLL L4) 256,
    Nat.blt (nN4) 1048576)))))))) = true := by quickRfl
theorem l4eq : L4 = [(e16 ())[0]!.toList, (e16 ())[1]!.toList] := by decide

end CertificateChecks.KernelSporSch.LySt

end
