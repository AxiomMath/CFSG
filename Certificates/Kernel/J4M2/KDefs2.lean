module

public import Certificates.Kernel.J4M2.KDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheckData

public section

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck

@[expose] noncomputable def qiL : List Nat :=
  [QI_0, QI_1, QI_2, QI_3, QI_4, QI_5, QI_6, QI_7, QI_8, QI_9, QI_10, QI_11]

@[expose] noncomputable def piK (m : Nat) : Nat :=
  (List.range 12).foldl (fun acc j => if m.testBit (11 - j) then mulJ c rm acc (getN one qiL (11 - j))
    else acc) one

@[expose] noncomputable def loL : List Nat := smapK pK (rangeK 64)

@[expose] noncomputable def hiL : List Nat := smapK (fun k => pK (64 * k)) (rangeK 64)

@[expose] noncomputable def loiL : List Nat := smapK piK (rangeK 64)

@[expose] noncomputable def hiiL : List Nat := smapK (fun k => piK (64 * k)) (rangeK 64)

@[expose] noncomputable def pT (lo hi : List Nat) (m : Nat) : Nat :=
  mulJ c rm (getN one lo (m % 64)) (getN one hi (m / 64))

@[expose] noncomputable def piT (lo hi : List Nat) (m : Nat) : Nat :=
  mulJ c rm (getN one hi (m / 64)) (getN one lo (m % 64))

@[expose] noncomputable def cK2 : Nat := mulJ c rm cK cK

@[expose] noncomputable def twoK (y a b : Nat) : Bool := orB (Nat.beq y a) (Nat.beq y b)

@[expose] noncomputable def closM (lo hi : List Nat) (m : Nat) : Bool :=
  strictB (pT lo hi m) fun p =>
    andB (allR 12 fun j => strictB (pT lo hi (m ^^^ 2 ^ j)) fun p' => strictB (mulJ c rm p' ZM) fun pz =>
        andB (twoK (mulJ c rm (getN one qaL j) p) p' pz) (twoK (mulJ c rm (getN one qiL j) p) p' pz))
      (andB (andB (Nat.blt (cMask m) 4096) (Nat.blt (cMask (cMask m)) 4096))
        (strictB (pT lo hi (cMask m)) fun p1 =>
          andB (twoK (mulJ c rm cK p) (mulJ c rm p1 cK) (mulJ c rm (mulJ c rm p1 ZM) cK))
            (strictB (pT lo hi (cMask (cMask m))) fun p2 =>
              twoK (mulJ c rm cK2 p) (mulJ c rm p2 cK2) (mulJ c rm (mulJ c rm p2 ZM) cK2))))

@[expose] noncomputable def closBlk (k : Nat) : Bool := allR 128 fun j => closM loL hiL (128 * k + j)

@[expose] noncomputable def closBlkHi (k : Nat) : Bool := closBlk (16 + k)

@[expose] noncomputable def iterJ (i x : Nat) : Nat := (List.range i).foldl (fun acc _ => mulJ c rm acc cK) x

@[expose] noncomputable def formK (f : Bool × Nat × Nat) : Nat :=
  iterJ f.2.2 (if f.1 then mulJ c rm (pK f.2.1) ZM else pK f.2.1)

@[expose] noncomputable def k3L : List Nat := k3F.map formK

@[expose] noncomputable def normK3K (k3 : List Nat) (x xi : Nat) : Bool :=
  k3.all fun y => strictB (mulJ c rm (mulJ c rm x y) xi) fun w => k3.any fun y' => Nat.beq w y'

@[expose] noncomputable def cinvK (i : Nat) : Nat := if i = 0 then one else if i = 1 then cK2 else cK

@[expose] noncomputable def normOne (p pi : Nat) (e : Bool) (m i : Nat) : Bool :=
  strictB (iterJ i (if e then mulJ c rm p ZM else p)) fun x =>
    strictB (mulJ c rm (cinvK i) (if e then mulJ c rm ZM pi else pi)) fun xi =>
      andB (andB (canonJ pad xi) (Nat.beq (mulJ c rm x xi) one))
        (orB (notB (normK3K k3L x xi)) (decide ((e, m, i) ∈ k3F)))

@[expose] noncomputable def normM (lo hi lo' hi' : List Nat) (m : Nat) : Bool :=
  strictB (pT lo hi m) fun p => strictB (piT lo' hi' m) fun pi =>
    andB (andB (andB (normOne p pi false m 0) (normOne p pi false m 1)) (normOne p pi false m 2))
      (andB (andB (normOne p pi true m 0) (normOne p pi true m 1)) (normOne p pi true m 2))

@[expose] noncomputable def normBlk (k : Nat) : Bool :=
  allR 128 fun j => normM loL hiL loiL hiiL (128 * k + j)

@[expose] noncomputable def normBlkHi (k : Nat) : Bool := normBlk (16 + k)

end CertificateChecks.KernelJ4M2

end
