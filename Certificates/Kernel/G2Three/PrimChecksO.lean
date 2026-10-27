module

public import Certificates.Data.Kernel.G2Three.Prim
public import Certificates.Data.G2ThreeMaxCheck
public import Certificates.Kernel.G2Three.PrimRec
public import Certificates.Kernel.G2Three.K7bRec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open Certificates.G2ThreeMax

theorem ch5182o_c : cK K7G (twG K7G outerInput.sigma) POCA POCB = true := by quickRfl

theorem ch5182o_x0 : Nat.beq (POX 0) (wA K7G outerInput.base) = true := by quickRfl

theorem ch5182o_h :
    hK (POX 0) K7G (twG K7G outerInput.sigma) POHA POHB (fun s => outerInput.stab.getD s []) 6 =
      true := by quickRfl

theorem ch5182o_root :
    rootK POX K7G (twG K7G outerInput.sigma) PORA PORB PORL PORC POROOTS 2808 9 1 = true := by
  quickRfl

theorem ch5182o_tr : trK POX PORA PORB POLAB POTP POTD POEU POEV 2808 9 2 = true := by quickRfl

theorem ch5182o_nt : ntK POX POCA POCB = true := by quickRfl

theorem ch5182o_cl0 : closK POX POCA POCB POIMG 2808 0 512 8 = true := by quickRfl
theorem ch5182o_cl1 : closK POX POCA POCB POIMG 2808 1 512 8 = true := by quickRfl
theorem ch5182o_cl2 : closK POX POCA POCB POIMG 2808 2 512 8 = true := by quickRfl
theorem ch5182o_cl3 : closK POX POCA POCB POIMG 2808 3 512 8 = true := by quickRfl
theorem ch5182o_cl4 : closK POX POCA POCB POIMG 2808 4 512 8 = true := by quickRfl
theorem ch5182o_cl5 : closK POX POCA POCB POIMG 2808 5 512 8 = true := by quickRfl

theorem ch5182o_fo0 : forK POX POHA POHB POLAB POHP POHS POROOTS 2808 6 9 0 512 8 = true := by
  quickRfl
theorem ch5182o_fo1 : forK POX POHA POHB POLAB POHP POHS POROOTS 2808 6 9 1 512 8 = true := by
  quickRfl
theorem ch5182o_fo2 : forK POX POHA POHB POLAB POHP POHS POROOTS 2808 6 9 2 512 8 = true := by
  quickRfl
theorem ch5182o_fo3 : forK POX POHA POHB POLAB POHP POHS POROOTS 2808 6 9 3 512 8 = true := by
  quickRfl
theorem ch5182o_fo4 : forK POX POHA POHB POLAB POHP POHS POROOTS 2808 6 9 4 512 8 = true := by
  quickRfl
theorem ch5182o_fo5 : forK POX POHA POHB POLAB POHP POHS POROOTS 2808 6 9 5 512 8 = true := by
  quickRfl

end CFSG.KD.G2Three

end
