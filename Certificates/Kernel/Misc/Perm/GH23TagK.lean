module

public import Certificates.Data.Kernel.Misc.PermGH23Tag
public import Certificates.Data.GH23Tags
public import Certificates.Kernel.Misc.Perm.GH23K
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Co1B.GenTri2045
public meta import Certificates.Kernel.Misc.Perm.GH23TagGen

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XE CFSG.KC.Misc.GH23TagGen.eXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XP CFSG.KC.Misc.GH23TagGen.pXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XS CFSG.KC.Misc.GH23TagGen.sXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XC CFSG.KC.Misc.GH23TagGen.cXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XN CFSG.KC.Misc.GH23TagGen.nXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XNG CFSG.KC.Misc.GH23TagGen.gnXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XO CFSG.KC.Misc.GH23TagGen.oXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XCO CFSG.KC.Misc.GH23TagGen.coXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XG CFSG.KC.Misc.GH23TagGen.gXL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.XB CFSG.KC.Misc.GH23TagGen.xbL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.JL CFSG.KC.Misc.GH23TagGen.jL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.JM CFSG.KC.Misc.GH23TagGen.jbL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.JO CFSG.KC.Misc.GH23TagGen.joL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.CW CFSG.KC.Misc.GH23TagGen.cwL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.W CFSG.KC.Misc.GH23TagGen.wL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.WO CFSG.KC.Misc.GH23TagGen.woL
#kss_natlist CertificateChecks.KernelMisc.GH23Tag.CNT CFSG.KC.Misc.GH23TagGen.cntL

namespace CertificateChecks.KernelMisc.GH23Tag

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23 CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
  CertificateChecks.KernelMisc.GH23

@[expose] noncomputable def gX (x j : Nat) : Nat := XG (Nat.add (Nat.mul 8 x) j)

@[expose] noncomputable def eX (x k : Nat) : Nat := XE (Nat.add (XO x) k)

@[expose] noncomputable def pX (x k : Nat) : Nat := XP (Nat.add (XO x) k)

@[expose] noncomputable def sX (x i : Nat) : Nat := XS (Nat.add (XO x) i)

@[expose] noncomputable def cX (x i : Nat) : Nat := XC (Nat.add (XCO x) i)

@[expose] noncomputable def xB (x : Nat) : Bool :=
  andB (allR 0 (XN x) (treeAt mul8 one8 (gX x) (XNG x) (eX x) (pX x)))
    (andB (allR 0 (XN x) (sortAt (XN x) (eX x) (sX x)))
      (allR 0 (XN x) (closedAt mul8 (gX x) (XNG x) (XN x) (eX x) (cX x))))

@[expose] noncomputable def gE (r k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (eX (Nat.sub r 42) k) (eM r k) (Nat.blt r 42)

@[expose] noncomputable def gN (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (XN (Nat.sub r 42)) (NN r) (Nat.blt r 42)

@[expose] noncomputable def gG (r j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (gX (Nat.sub r 42) j) (gM r j) (Nat.blt r 42)

@[expose] noncomputable def gNG (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (XNG (Nat.sub r 42)) (NG r) (Nat.blt r 42)

@[expose] noncomputable def refGens (r : Nat) : List Nat := (List.range (gNG r)).map (gG r)

@[expose] noncomputable def jA (j : Nat) : Nat := JL (Nat.mul 2 j)

@[expose] noncomputable def jB (j : Nat) : Nat := JL (Nat.add (Nat.mul 2 j) 1)

@[expose] noncomputable def jobB (j : Nat) : Bool :=
  allR 0 (Nat.mul (gN (jA j)) (gN (jA j)))
    (commAt (gE (jA j)) (gN (jA j)) (gE (jB j)) (gN (jB j)) CW (JO j))

@[expose] noncomputable def wM (m i : Nat) : Nat := W (Nat.add (WO m) i)

@[expose] noncomputable def memR (r c t : Nat) : Bool := memAt (gE r) (gN r) c t

@[expose] noncomputable def solvW (m : Nat) (chain : List (List Nat)) : Bool :=
  chain.getLast? == some [] && (List.range chain.length).all fun k =>
    decide (XB m + k < 42 + CNT 0) && refGens (XB m + k) == chain.getD k [] &&
      decide (JM m + k < CNT 1) && jA (JM m + k) == (if k = 0 then m else XB m + k - 1) &&
      jB (JM m + k) == XB m + k

@[expose] noncomputable def twoW (w : Nat → Nat) (m : Nat) (ngens : List Nat) : Bool :=
  decide (XB m < 42 + CNT 0) && refGens (XB m) == ngens && ngens.any (· != one8) &&
    (List.range ngens.length).all (fun i => memR m (ngens.getD i 0) (w i)) &&
    (List.range (gN (XB m))).all (fun k => mul8 (gE (XB m) k) (gE (XB m) k) == one8) &&
    (List.range (NG m)).all fun j => (List.range ngens.length).all fun i =>
      decide (w (ngens.length + 2 * (j * ngens.length + i)) < gN (XB m)) &&
        mul8 (gM m j) (ngens.getD i 0) ==
          mul8 (gE (XB m) (w (ngens.length + 2 * (j * ngens.length + i)))) (gM m j) &&
        decide (w (ngens.length + 2 * (j * ngens.length + i) + 1) < gN (XB m)) &&
        mul8 (ngens.getD i 0) (gM m j) ==
          mul8 (gM m j) (gE (XB m) (w (ngens.length + 2 * (j * ngens.length + i) + 1)))

@[expose] noncomputable def isoW (w : Nat → Nat) (m : Nat) (imgs : List Nat) (sz : Nat) : Bool :=
  decide (XB m < 42 + CNT 0) && refGens (XB m) == imgs && gN (XB m) == sz &&
    (List.range imgs.length).all (fun i => memR m (imgs.getD i 0) (w i)) &&
    (List.range (NG m)).all fun j => memR (XB m) (gM m j) (w (imgs.length + j))

@[expose] noncomputable def idx2W (w : Nat → Nat) (m j : Nat) : Bool :=
  decide (j < 41) && NN m == 2 * NN j &&
    (match (members.getD j ⟨[], .top⟩).tag with | .z3a5 _ _ => true | _ => false) &&
    (List.range (NG j)).all fun i => memR m (gM j i) (w i)

@[expose] noncomputable def glW (w : Nat → Nat) (m : Nat) : Bool :=
  NN m == NN 41 && eM m 0 == one8 && eM 41 (w 0) == one8 &&
    (List.range (NN m)).all fun k =>
      decide (w k < NN 41) && w (NN m + w k) == k &&
        (List.range (NG m)).all fun j =>
          eM 41 (w (cM m (k * NG m + j))) == mul8 (eM 41 (w k)) (eM 41 (w (cM m j)))

@[expose] noncomputable def tagW (m : Nat) : Bool :=
  match (members.getD m ⟨[], .top⟩).tag with
  | .solv chain => solvW m chain
  | .two ngens => twoW (wM m) m ngens
  | .alt n imgs => (n == 5 || n == 6 || n == 7) && decide (imgs.length + 2 = n) &&
      carmRels imgs && isoW (wM m) m imgs (fact n / 2)
  | .sym n imgs => (n == 5 || n == 6) && decide (imgs.length + 1 = n) && coxRels imgs &&
      isoW (wM m) m imgs (fact n)
  | .z3a5 imgs z => decide (imgs.length = 3) && carmRels imgs && mulC (mulC z z) z == oneC &&
      imgs.all (fun x => mulC z x == mulC x z) && isoW (wM m) m (imgs ++ [z]) 180
  | .idx2 j => idx2W (wM m) m j
  | .gl _ => glW (wM m) m
  | .top => (members.getD m ⟨[], .top⟩).gens == topGens

theorem cnt_ok : CNT 0 = 49 ∧ CNT 1 = 27 := by decide +kernel

theorem xvalid : ∀ x < 49, (refGens (42 + x)).all validC = true := by decide +kernel

end CertificateChecks.KernelMisc.GH23Tag

#kc_slices CertificateChecks.KernelMisc.GH23Tag.XK CertificateChecks.KernelMisc.GH23Tag.xB 49
#kc_slices CertificateChecks.KernelMisc.GH23Tag.JK CertificateChecks.KernelMisc.GH23Tag.jobB 27
#kc_slices CertificateChecks.KernelMisc.GH23Tag.TW CertificateChecks.KernelMisc.GH23Tag.tagW 41

end
