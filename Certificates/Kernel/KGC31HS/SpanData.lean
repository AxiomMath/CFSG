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

meta def uOrbLab (ws : List (List Int)) : List Nat :=
  let bs := ws.map gw
  let es := (List.range (2 ^ bs.length)).map (maskA bs)
  [CFSG.KS.RawGen.pack 7 ((Array.range 100).map fun q => es.foldl (fun a e => min a e[q]!) q)]

meta def ol16 : List Nat := uOrbLab u16W
meta def ol8 : List Nat := uOrbLab u8W

meta def ptab (ws : List (List Int)) : List Nat :=
  let bs := ws.map gw
  let es := (List.range (2 ^ bs.length)).map (maskA bs)
  (List.range 100).map fun x =>
    (List.range es.length).foldl (fun a m => a ||| (1 <<< (16 * (es[m]!)[x]! + 16 + m))) x

meta def pt16 : List Nat := ptab u16W
meta def pt8 : List Nat := ptab u8W

end CertificateChecks.KernelKGC31HS.SpanE

public section

#kss_natlist CertificateChecks.KernelKGC31HS.SP16 CertificateChecks.KernelKGC31HS.SpanE.s16
#kss_natlist CertificateChecks.KernelKGC31HS.SP8 CertificateChecks.KernelKGC31HS.SpanE.s8
#kss_natlist CertificateChecks.KernelKGC31HS.B16 CertificateChecks.KernelKGC31HS.SpanE.b16
#kss_natlist CertificateChecks.KernelKGC31HS.B8 CertificateChecks.KernelKGC31HS.SpanE.b8
#kss_natlist CertificateChecks.KernelKGC31HS.R16 CertificateChecks.KernelKGC31HS.SpanE.r16
#kss_natlist CertificateChecks.KernelKGC31HS.R8 CertificateChecks.KernelKGC31HS.SpanE.r8
#kss_natlist CertificateChecks.KernelKGC31HS.OrbL16 CertificateChecks.KernelKGC31HS.SpanE.ol16
#kss_natlist CertificateChecks.KernelKGC31HS.OrbL8 CertificateChecks.KernelKGC31HS.SpanE.ol8
#kss_natlist CertificateChecks.KernelKGC31HS.PT16 CertificateChecks.KernelKGC31HS.SpanE.pt16
#kss_natlist CertificateChecks.KernelKGC31HS.PT8 CertificateChecks.KernelKGC31HS.SpanE.pt8

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CFSG.Quasithin.KGC31.HS

@[expose] noncomputable def ptEq (T b s : Nat) : Bool :=
  allN 100 fun p => Nat.beq (pg 7 (mask 7) T (pg 7 (mask 7) b p)) (pg 7 (mask 7) s (pg 7 (mask 7) T p))

@[expose] noncomputable def ptB5 (T b s : Nat) : Bool :=
  allN 5 fun p => Nat.beq (pg 7 (mask 7) T (pg 7 (mask 7) b p)) (pg 7 (mask 7) s (pg 7 (mask 7) T p))

@[expose] noncomputable def pnormT (nb ns : Nat) (B S : Nat → Nat) (T : Nat) : Bool :=
  ((List.range nb).map B).all fun b => ((List.range ns).map S).any fun s => ptEq T b s

@[expose] noncomputable def tbit (w y m : Nat) : Bool := Nat.beq ((w >>> (16 * y + 16 + m)) % 2) 1

@[expose] noncomputable def pnormL (nb ns : Nat) (B S P : Nat → Nat) (T : Nat) : Bool :=
  ((List.range nb).map B).all fun b => (List.range ns).any fun m =>
    tbit (P (pg 7 (mask 7) T 0)) (pg 7 (mask 7) T (pg 7 (mask 7) b 0)) m &&
      ptB5 T b (S m)

@[expose] noncomputable def preFT (nb : Nat) (B : Nat → Nat) (L : Nat) (τ : Nat → Nat) : Bool :=
  ((List.range nb).map B).all fun b =>
    Nat.beq (pg 7 (mask 7) L (τ (pg 7 (mask 7) b 0))) (pg 7 (mask 7) L (τ 0))

@[expose] noncomputable def pnormF (nb ns : Nat) (B S P : Nat → Nat) (τ : Nat → Nat) : Bool :=
  ((List.range nb).map B).all fun b => (List.range ns).any fun m =>
    tbit (P (τ 0)) (τ (pg 7 (mask 7) b 0)) m &&
      allN 5 fun p => Nat.beq (τ (pg 7 (mask 7) b p)) (pg 7 (mask 7) (S m) (τ p))

@[expose] noncomputable def cosF (f : (Nat → Nat) → Bool) : List (List Nat) → (Nat → Nat) → Nat
  | [], _ => 0
  | [T], g => T.countP fun t => f fun x => g (pg 7 (mask 7) t x)
  | T :: T' :: Ts, g => T.foldl (fun a t => a + cosF f (T' :: Ts) fun x => g (pg 7 (mask 7) t x)) 0

@[expose] noncomputable def cosT (nb ns : Nat) (B S R P : Nat → Nat) (K : Nat → Nat) (L i : Nat) : Bool :=
  Nat.beq (cosF (fun τ => preFT nb B L τ && pnormF nb ns B S P τ)
    (trPL 100 7 CCA.LR CCA.TR 3) (pg 7 (mask 7) (R i))) (K i)

@[expose] noncomputable def cos16T (i : Nat) : Bool := cosT 4 16 B16 SP16 R16 PT16 K16 (OrbL16 0) i

@[expose] noncomputable def cos8T (i : Nat) : Bool := cosT 3 8 B8 SP8 R8 PT8 K8 (OrbL8 0) i

theorem kPT : (((List.range 16).all fun m => allN 100 fun x =>
      tbit (PT16 x) (pg 7 (mask 7) (SP16 m) x) m) &&
    ((List.range 8).all fun m => allN 100 fun x => tbit (PT8 x) (pg 7 (mask 7) (SP8 m) x) m)) = true := by
  quickRfl

theorem kOrbL : (((List.range 16).all fun m => allN 100 fun q =>
      Nat.beq (pg 7 (mask 7) (OrbL16 0) (pg 7 (mask 7) (SP16 m) q)) (pg 7 (mask 7) (OrbL16 0) q)) &&
    ((List.range 8).all fun m => allN 100 fun q =>
      Nat.beq (pg 7 (mask 7) (OrbL8 0) (pg 7 (mask 7) (SP8 m) q)) (pg 7 (mask 7) (OrbL8 0) q))) = true := by
  quickRfl

theorem kRec : ((List.range 16).all (fun m => Nat.beq (SP16 m) (pmask 100 7 u16P m)) &&
    (List.range 8).all (fun m => Nat.beq (SP8 m) (pmask 100 7 u8P m)) &&
    (List.range 4).all (fun j => Nat.beq (B16 j) (pw (u16W.getD j []))) &&
    (List.range 3).all (fun j => Nat.beq (B8 j) (pw (u8W.getD j []))) &&
    (List.range 15).all (fun i => Nat.beq (R16 i) (pw (u16CosetW.getD i []))) &&
    (List.range 7).all (fun i => Nat.beq (R8 i) (pw (u8CosetW.getD i [])))) = true := by quickRfl

end CertificateChecks.KernelKGC31HS

end
