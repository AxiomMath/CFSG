
module

public import Certificates.Data.Kernel.MonsterB.FischerBT
public import CFSG.Monster.B.TwoA.Fischer.CertBin
public import CFSG.Monster.B.TwoA.Fischer.CertData
public import Certificates.Data.Kernel.MonsterB.FischerK
public import Certificates.Kernel.MonsterB.FischerData3067

public section

namespace CertificateChecks.KernelMonB.F3067

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.KC.FischerK
  CFSG.KC.FischerB CFSG.KLie.CT

@[expose] noncomputable def orbitDataB : BT × BT × BT × BT := Id.run do
  let mut idx : BT := mkB 2048 11
  let mut dist : BT := mkB 0 11
  let mut par : BT := mkB 0 11
  let mut gen : BT := mkB 0 11
  let mut t := 0
  for s in [0:2048] do
    if getT idx s == 2048 then
      idx := setT idx s t
      let mut queue : Array ℕ := #[s]
      let mut qn := 1
      let mut h := 0
      for _ in [0:2048] do
        if h < qn then
          let u := queue[h]!
          for k in [0:2] do
            let x := vecMulL (fColArr[k]!).toList u
            if x < 2048 && getT idx x == 2048 then
              idx := setT idx x t
              dist := setT dist x (getT dist u + 1)
              par := setT par x u
              gen := setT gen x k
              queue := queue.push x
              qn := qn + 1
          h := h + 1
      t := t + 1
  return (idx, dist, par, gen)

@[expose] noncomputable def orbChkB (D : BT × BT × BT × BT) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun a r => Prod.rec (motive := fun _ => Bool)
    (fun b r => Prod.rec (motive := fun _ => Bool) (fun c d =>
      allN 2048 fun m => getT a m == fget (FD.ORB[0]!) m 11 && getT b m == fget (FD.ORB[1]!) m 11 &&
        getT c m == fget (FD.ORB[2]!) m 11 && getT d m == fget (FD.ORB[3]!) m 11) r) r) D

end CertificateChecks.KernelMonB.F3067

end
