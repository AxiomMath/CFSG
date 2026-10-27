module

public import Certificates.Kernel.SporSch.Ru.B1X
public import Certificates.Kernel.SporSch.Ru.SmallChains
public import Certificates.Kernel.SporSch.Ru.CChain
meta import CFSG.Sporadic.Schreier.RuCheckCentersInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuCt

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def rfM : Array (Array Nat) := (Array.range 7).map ruEF

meta def conj1920 (g x : Array Nat) : Array Nat := compA 1920 (compA 1920 g x) (invCand 1920 g)

meta def orbitM : Array (Array (Array Nat)) × Array Nat × Array Nat := Id.run do
  let gens := #[(ruField1920 0)[0]!, (ruField1920 0)[1]!]
  let mut seen : Array (Array (Array Nat)) := #[rfM]
  let mut par : Array Nat := #[0]
  let mut gen : Array Nat := #[0]
  let mut head := 0
  for _ in [0:200] do
    if head < seen.size then
      let t := seen[head]!
      for g in [0:2] do
        let u := t.map (conj1920 gens[g]!)
        if !(seen.any fun s => s == u) then
          seen := seen.push u
          par := par.push head
          gen := gen.push g
      head := head + 1
  return (seen, par, gen)

meta def toM : Array (Array Nat) := orbitM.1.foldl (fun acc t => acc ++ t) #[]

meta def parM : Array Nat := orbitM.2.1

meta def genM : Array Nat := orbitM.2.2

end CertificateChecks.KernelSporSch.RuCt

#kss_perms CertificateChecks.KernelSporSch.RuCt.RF 11 CertificateChecks.KernelSporSch.RuCt.rfM
#kss_perms CertificateChecks.KernelSporSch.RuCt.TO 11 CertificateChecks.KernelSporSch.RuCt.toM
#ks_perm CertificateChecks.KernelSporSch.RuCt.PARP 7 CertificateChecks.KernelSporSch.RuCt.parM
#ks_perm CertificateChecks.KernelSporSch.RuCt.GENP 7 CertificateChecks.KernelSporSch.RuCt.genM

namespace CertificateChecks.KernelSporSch.RuCt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuB1K CertificateChecks.KernelSporSch.RuLines

@[expose] noncomputable def qc (p q : Nat) : Nat := pcomp 1920 11 (mask 11) p q

@[expose] noncomputable def parT (k : Nat) : Nat := pg 7 (mask 7) PARP k

@[expose] noncomputable def genT (k : Nat) : Nat := pg 7 (mask 7) GENP k

@[expose] noncomputable def tstep (k : Nat) : Bool :=
  bIf(Nat.beq k 0, true, strictB (parT k) (fun p => strictB (genT k) (fun g =>
    bAnd(Nat.blt p k, bAnd(Nat.blt g 2, allN 7 (fun i =>
      Nat.beq (qc (qc (gen2 (RuT1920.L 0) (RuT1920.L 1) g) (TO (Nat.add (Nat.mul 7 p) i)))
          (gen2 (RuLI1920 0) (RuLI1920 1) g))
        (TO (Nat.add (Nat.mul 7 k) i))))))))

@[expose] noncomputable def tdist (k : Nat) : Bool :=
  allN k (fun k' => !allN 7 (fun i =>
    Nat.beq (TO (Nat.add (Nat.mul 7 k) i)) (TO (Nat.add (Nat.mul 7 k') i))))

@[expose] noncomputable def cm (G X : Nat) : Bool := Nat.beq (qc G X) (qc X G)

@[expose] noncomputable def zkpK (G : Nat) : Bool :=
  bIf(allN 8 (fun k => cm G (RuT1920.L (Nat.add 14 k))),
    bIf(Nat.beq G (pidn 1920 11), true, anyK 7 (fun i => Nat.beq G (RF i))), true)

@[expose] noncomputable def cjpK (G : Nat) : Bool :=
  bIf(allN 6 (fun j => cm G (RuT1920.L (Nat.add 24 j))),
    bAnd(Nat.beq (Nat.shiftRight G (1920 * 11)) 0,
      siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuJS2.LR RuJS2.TRI RuJS2.BP 2 0 G), true)

@[expose] noncomputable def zkRow (a : Nat) : Bool :=
  row2K 1920 11 (mask 11) (1920 * 11) RuKS.LR RuKS.TR zkpK a

@[expose] noncomputable def cjRow (a : Nat) : Bool :=
  row2K 1920 11 (mask 11) (1920 * 11) RuKS.LR RuKS.TR cjpK a

@[expose] noncomputable def tcan (k : Nat) : Bool :=
  allN 7 (fun i => canonK 1920 11 (mask 11) (1920 * 11) (TO (Nat.add (Nat.mul 7 k) i)))

end CertificateChecks.KernelSporSch.RuCt

namespace CertificateChecks.KernelSporSch.RuCt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuB1K CertificateChecks.KernelSporSch.RuLines

theorem e0 : Nat.beq (EA 0) Z = true := by quickRfl
theorem eInv : allN 7 (fun i => permOK 4060 12 (mask 12) (4060 * 12) (EA i) (EA i)) = true := by
  quickRfl
theorem eNe : allN 7 (fun i => !Nat.beq (EA i) (pidn 4060 12)) = true := by quickRfl
theorem eDist : allN 7 (fun i => allN 7 (fun j => Nat.beq i j || !Nat.beq (EA i) (EA j))) = true := by
  quickRfl
theorem eProd : allN 7 (fun i => allN 7 (fun j => Nat.beq i j ||
    anyK 7 (fun k => Nat.beq (pc (EA i) (EA j)) (EA k)))) = true := by quickRfl
theorem eComm : allN 7 (fun i => allN 7 (fun j =>
    Nat.beq (pc (EA i) (EA j)) (pc (EA j) (EA i)))) = true := by quickRfl
theorem eSq : allN 7 (fun i => Nat.beq (pc (EA i) (EA i)) (pidn 4060 12)) = true := by quickRfl
theorem eConj : allN 7 (fun i => allN 2 (fun g =>
    anyK 7 (fun j => Nat.beq (CFSG.KS.SporSch.conjP (gen2 Ns0 Ns1 g) (gen2 Ns0I Ns1I g) (EA i)) (EA j)))) = true := by
  quickRfl
theorem eLens : bAnd(Nat.beq (lenNL (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.1) 7,
    Nat.beq (lenNL (ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.2) 7) = true := by quickRfl
theorem eTree : allN 7 (fun i => Nat.beq i 0 ||
    (strictB ((ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.1.getD i 0) (fun p =>
      strictB ((ebfsK Ns0 Ns1 Ns0I Ns1I Z).2.2.getD i 0) (fun g =>
      bAnd(Nat.blt p i, bAnd(Nat.blt g 2,
        Nat.beq (EA i) (CFSG.KS.SporSch.conjP (gen2 Ns0 Ns1 g) (gen2 Ns0I Ns1I g) (EA p)))))))) = true := by
  quickRfl
theorem eSiftC : allN 7 (fun i => bAnd(Nat.beq (Nat.shiftRight (EA i) (4060 * 12)) 0,
    siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuCS.LR RuCS.TRI RuCS.BP 3 0 (EA i))) = true := by
  quickRfl
theorem eKcomm : allN 7 (fun i => allN 8 (fun k =>
    Nat.beq (pc (EA i) (RuCe.KG k)) (pc (RuCe.KG k) (EA i)))) = true := by quickRfl

theorem rfOK : allN 7 (fun i => resK 1920 12 11 RuF.F RuF.FPOS (EA i) (RF i)) = true := by quickRfl
theorem rfPerm : allN 7 (fun i => permOK 1920 11 (mask 11) (1920 * 11) (RF i) (RF i)) = true := by
  quickRfl
theorem rfSiftK : allN 7 (fun i => bAnd(Nat.beq (Nat.shiftRight (RF i) (1920 * 11)) 0,
    siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuKS.LR RuKS.TRI RuKS.BP 2 0 (RF i))) = true := by
  quickRfl
theorem rfSiftJ : allN 7 (fun i => bAnd(Nat.beq (Nat.shiftRight (RF i) (1920 * 11)) 0,
    siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuJS2.LR RuJS2.TRI RuJS2.BP 2 0 (RF i))) = true := by
  quickRfl

theorem t0 : allN 7 (fun i => Nat.beq (TO i) (RF i)) = true := by quickRfl
theorem kH : allN 10 (fun j => bAnd(Nat.beq (Nat.shiftRight (RuKS.S j) (1920 * 11)) 0,
    siftK 1920 11 (mask 11) (1920 * 11) (pidn 1920 11) RuFS.LR RuFS.TRI RuFS.BP 2 0 (RuKS.S j))) =
    true := by quickRfl
theorem kX : allN 10 (fun j => allN 7 (fun i => cm (RuKS.S j) (RF i))) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuCt

end
