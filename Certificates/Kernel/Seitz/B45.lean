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
meta def arrs : Array (Array Nat) :=
  #[invArr, repArr, labArr, repsArr, isUArr.map fun b => if b then 1 else 0]

open CFSG.KC.Eval in
meta def natsV (l : List Nat) : Val := .list (l.toArray.map .nat)

open CFSG.KC.Eval in
meta def plan : Step := fun args => do
  let cap : Nat := match args[0]? with
    | some (Val.nat c) => c
    | _ => 1200000
  let mt := mtF
  let lab := labF
  let invs := (List.range 256).filter fun i => mt i i == 0
  let masks := (List.range 65536).filter fun m => admM laddF m
  let mut st : Array Val := #[]
  let mut sl : Array Val := #[]
  let mut idx : Nat := 0
  for m in masks do
    let tl := tauList lab m
    let os := ordStats mt tl
    let zt := zOf mt tl
    st := st.push (natsV ([tl.length] ++ os ++ [zt]))
    let work : Nat → Nat → Nat := fun a b =>
      if (a == 0 && b == 0) || !(inM m (lab a) (lab b)) then 1 else
        let L := cenList mt lab m a b
        512 + L.length + (if L.length == tl.length then 8 * L.length +
          (if ordStats mt L == os then L.length * L.length else 0) else 0)
    let mut cur : Option (Nat × Nat) := none
    let mut acc : Nat := 0
    for a in invs do
      let wa : Nat := invs.foldl (fun s b => s + work a b) 0
      if Nat.blt cap wa then
        match cur with
        | some (lo, hi) => sl := sl.push (natsV [idx, lo, hi, 0, 256]); cur := none; acc := 0
        | none => pure ()
        let mut blo : Nat := 0
        let mut bacc : Nat := 0
        for b in invs do
          let w : Nat := work a b
          if Nat.blt cap (bacc + w) && Nat.blt 0 bacc then
            sl := sl.push (natsV [idx, a, a + 1, blo, b])
            blo := b
            bacc := 0
          bacc := bacc + w
        sl := sl.push (natsV [idx, a, a + 1, blo, 256])
      else
        match cur with
        | some (lo, _) =>
          if Nat.blt cap (acc + wa) then
            sl := sl.push (natsV [idx, lo, a, 0, 256])
            cur := some (a, a + 1)
            acc := wa
          else
            cur := some (lo, a + 1)
            acc := acc + wa
        | none => cur := some (a, a + 1); acc := wa
    match cur with
    | some (lo, _) => sl := sl.push (natsV [idx, lo, 256, 0, 256])
    | none => pure ()
    idx := idx + 1
  return #[(`MS, natsV masks), (`ST, .list st), (`SL, .list sl)]

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

@[expose] noncomputable def sliceK (c : Nat) : Bool :=
  let s := P6.SL.getD c []
  let st := P6.ST.getD (s.getD 0 0) []
  sliceF mtT labT (P6.MS.getD (s.getD 0 0) 0) (st.getD 0 0)
    [st.getD 1 0, st.getD 2 0, st.getD 3 0, st.getD 4 0] (st.getD 5 0)
    (s.getD 1 0) (s.getD 2 0) (s.getD 3 0) (s.getD 4 0)

@[expose] noncomputable def statsK (i : Nat) : Bool :=
  let st := P6.ST.getD i []
  statsF mtT labT (P6.MS.getD i 0) (st.getD 0 0)
    [st.getD 1 0, st.getD 2 0, st.getD 3 0, st.getD 4 0] (st.getD 5 0)

@[expose] noncomputable def admK (c : Nat) : Bool := admOK laddT P6.MS (4096 * c) 4096

end CertificateChecks.KernelSeitz

end
