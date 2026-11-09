module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Seitz77B45K
meta import Certificates.Data.Seitz77CaseB45Data
public meta import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Eval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSeitz.B45

open CFSG.PSL3Four.Native Certificates.Seitz77CaseB45

meta def tlM : Array (Array Nat) := tlGens
meta def uM : Array (Array Nat) := uGens
meta def idM : Array Nat := idTab 42
meta def mtRows : Array (Array Nat) :=
  (Array.range 256).map fun i => (Array.range 256).map fun j => mtF i j
meta def orbRep (a : Nat) : Nat × Nat :=
  if mtF a a != 0 then (a, 0) else
  let U := (List.range 256).filter fun g => labF g == 0
  let r := (U.map fun g => mtF (mtF g a) invArr[g]!).foldl min a
  (r, (U.find? fun g => mtF (mtF g r) invArr[g]! == a).getD 0)

meta def arrs : Array (Array Nat) :=
  #[invArr, repArr, labArr, repsArr, isUArr.map fun b => if b then 1 else 0,
    (Array.range 256).map fun a => (orbRep a).1, (Array.range 256).map fun a => (orbRep a).2]

open CFSG.KC.Eval in
meta def natsV (l : List Nat) : Val := .list (l.toArray.map .nat)

open CFSG.KC.Eval in
meta def plan : Step := fun _ => do
  let mt := mtF
  let lab := labF
  let invs := (List.range 256).filter fun i => mt i i == 0
  let masks := (List.range 65536).filter fun m => admM laddF m
  let mut st : Array Val := #[]
  let mut sl : Array Val := #[]
  let mut zw : Array Val := #[]
  let mut idx : Nat := 0
  for m in masks do
    let tl := tauList lab m
    let os := ordStats mt tl
    let zt := zOf mt tl
    st := st.push (natsV ([tl.length] ++ os ++ [zt]))
    sl := sl.push (natsV [idx, 0, 256, 0, 256])
    for a in invs do
      for b in invs do
        if !(a == 0 && b == 0) && inM m (lab a) (lab b) && (orbRep a).1 == a &&
            (orbRep b).1 == b then
          let L := cenList mt lab m a b
          if L.length == tl.length && ordStats mt L == os && Nat.blt zt (zOf mt L) then
            let cen := (List.range L.length).filter fun i =>
              let w := L.getD i wone
              L.all fun v => wmul mt w v == wmul mt v w
            let quick := fun (i : Nat) =>
              let w := L.getD i wone
              let x := w.1
              let y := w.2.1
              let fl := fun (u v : Nat) => (List.range 256).filter fun c => mt u c == mt c v
              !w.2.2 && (fl a a).all (fun c => mt x c == mt c x) &&
                (fl b b).all (fun d => mt y d == mt d y) &&
                (fl a b).all (fun c => mt x c == mt c y) && (fl b a).all (fun d => mt y d == mt d x)
            let pick := cen.filter quick ++ cen.filter fun i => !(quick i)
            zw := zw.push (natsV ([a, b] ++ pick.take (zt + 1)))
    idx := idx + 1
  return #[(`MS, natsV masks), (`ST, .list st), (`SL, .list sl), (`ZW, .list zw)]

end CertificateChecks.KernelSeitz.B45

#kpenum CertificateChecks.KernelSeitz.TLE 42 6 false CertificateChecks.KernelSeitz.B45.tlM
  CertificateChecks.KernelSeitz.B45.tlM CertificateChecks.KernelSeitz.B45.idM 256
#kpenum CertificateChecks.KernelSeitz.UE 42 6 false CertificateChecks.KernelSeitz.B45.uM
  CertificateChecks.KernelSeitz.B45.uM CertificateChecks.KernelSeitz.B45.idM 64
#kmisc_packarrs CertificateChecks.KernelSeitz.MTR CertificateChecks.KernelSeitz.B45.mtRows 8
#kmisc_packarrs CertificateChecks.KernelSeitz.B45A CertificateChecks.KernelSeitz.B45.arrs 8
#kc_eval CertificateChecks.KernelSeitz P6 CertificateChecks.KernelSeitz.B45.plan 1200000

namespace CertificateChecks.KernelSeitz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.SeitzB45

@[expose] noncomputable def mtT : Nat → Nat → Nat := mtB MTR
@[expose] noncomputable def labT : Nat → Nat := vB (B45A 2)
@[expose] noncomputable def laddT : Nat → Nat → Nat := laddB MTR (B45A 2) (B45A 3)
@[expose] noncomputable def isUT : Nat → Bool := uB (B45A 4)
@[expose] noncomputable def invT : Nat → Nat := vB (B45A 0)
@[expose] noncomputable def crT : Nat → Nat := vB (B45A 5)
@[expose] noncomputable def cgT : Nat → Nat := vB (B45A 6)

@[expose] noncomputable def sliceK (c : Nat) : Bool :=
  let s := P6.SL.getD c []
  let st := P6.ST.getD (s.getD 0 0) []
  sliceO mtT labT crT (P6.MS.getD (s.getD 0 0) 0) (st.getD 0 0)
    [st.getD 1 0, st.getD 2 0, st.getD 3 0, st.getD 4 0] (st.getD 5 0) P6.ZW
    (s.getD 1 0) (s.getD 2 0) (s.getD 3 0) (s.getD 4 0)

@[expose] noncomputable def statsK (i : Nat) : Bool :=
  let st := P6.ST.getD i []
  statsF mtT labT (P6.MS.getD i 0) (st.getD 0 0)
    [st.getD 1 0, st.getD 2 0, st.getD 3 0, st.getD 4 0] (st.getD 5 0)

@[expose] noncomputable def admK (c : Nat) : Bool := admOK laddT P6.MS (4096 * c) 4096

end CertificateChecks.KernelSeitz

end
