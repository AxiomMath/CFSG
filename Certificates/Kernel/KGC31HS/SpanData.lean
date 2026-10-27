module

public import Certificates.Kernel.KGC31HS.Defs
public import Certificates.Kernel.KGC31HS.CosData
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Kernel.KGC31HS.Data
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelKGC31HS.SpanE

open CFSG.KS.SporSch.MOCG CFSG.Quasithin.KGC31.HS CertificateChecks.KernelKGC31HS

meta def maskA : List (Array Nat) → Nat → Array Nat
  | [], _ => idA 100
  | b :: bs, m => comp (if m % 2 = 1 then b else idA 100) (maskA bs (m / 2))

meta def span (ws : List (List Int)) : List Nat :=
  let bs := ws.map gw
  (List.range (2 ^ bs.length)).map fun m => CFSG.KS.RawGen.pack 7 (maskA bs m)

meta def packs (ws : List (List Int)) : List Nat := ws.map fun w => CFSG.KS.RawGen.pack 7 (gw w)

meta def s16 : List Nat := span u16W
meta def s8 : List Nat := span u8W
meta def b16 : List Nat := packs u16W
meta def b8 : List Nat := packs u8W
meta def r16 : List Nat := packs u16CosetW
meta def r8 : List Nat := packs u8CosetW

end CertificateChecks.KernelKGC31HS.SpanE

public section

#kss_natlist CertificateChecks.KernelKGC31HS.SP16 CertificateChecks.KernelKGC31HS.SpanE.s16
#kss_natlist CertificateChecks.KernelKGC31HS.SP8 CertificateChecks.KernelKGC31HS.SpanE.s8
#kss_natlist CertificateChecks.KernelKGC31HS.B16 CertificateChecks.KernelKGC31HS.SpanE.b16
#kss_natlist CertificateChecks.KernelKGC31HS.B8 CertificateChecks.KernelKGC31HS.SpanE.b8
#kss_natlist CertificateChecks.KernelKGC31HS.R16 CertificateChecks.KernelKGC31HS.SpanE.r16
#kss_natlist CertificateChecks.KernelKGC31HS.R8 CertificateChecks.KernelKGC31HS.SpanE.r8

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CFSG.Quasithin.KGC31.HS

@[expose] noncomputable def ptEq (T b s : Nat) : Bool :=
  allN 100 fun p => Nat.beq (pg 7 (mask 7) T (pg 7 (mask 7) b p)) (pg 7 (mask 7) s (pg 7 (mask 7) T p))

@[expose] noncomputable def pnormT (nb ns : Nat) (B S : Nat → Nat) (T : Nat) : Bool :=
  ((List.range nb).map B).all fun b => ((List.range ns).map S).any fun s => ptEq T b s

@[expose] noncomputable def cosT (nb ns : Nat) (B S R : Nat → Nat) (K : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (cbP.countP fun c => pnormT nb ns B S (pc 100 7 (R i) c)) (K i)

@[expose] noncomputable def cos16T (i : Nat) : Bool := cosT 4 16 B16 SP16 R16 K16 i

@[expose] noncomputable def cos8T (i : Nat) : Bool := cosT 3 8 B8 SP8 R8 K8 i

theorem kRec : ((List.range 16).all (fun m => Nat.beq (SP16 m) (pmask 100 7 u16P m)) &&
    (List.range 8).all (fun m => Nat.beq (SP8 m) (pmask 100 7 u8P m)) &&
    (List.range 4).all (fun j => Nat.beq (B16 j) (pw (u16W.getD j []))) &&
    (List.range 3).all (fun j => Nat.beq (B8 j) (pw (u8W.getD j []))) &&
    (List.range 15).all (fun i => Nat.beq (R16 i) (pw (u16CosetW.getD i []))) &&
    (List.range 7).all (fun i => Nat.beq (R8 i) (pw (u8CosetW.getD i [])))) = true := by quickRfl

end CertificateChecks.KernelKGC31HS

end
