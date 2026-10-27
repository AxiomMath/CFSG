module

public import Certificates.Data.Kernel.G2Three.Prim
public import Certificates.Data.G2ThreeMaxCheck
public import Certificates.Kernel.G2Three.PrimRec
public import Certificates.Kernel.G2Three.K7bRec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open Certificates.G2ThreeMax

theorem ch5182i_c : cK K7G (twG K7G innerInput.sigma) PICA PICB = true := by quickRfl

theorem ch5182i_x0 : Nat.beq (PIX 0) (wA K7G innerInput.base) = true := by quickRfl

theorem ch5182i_h :
    hK (PIX 0) K7G (twG K7G innerInput.sigma) PIHA PIHB (fun s => innerInput.stab.getD s []) 10 =
      true := by quickRfl

theorem ch5182i_root :
    rootK PIX K7G (twG K7G innerInput.sigma) PIRA PIRB PIRL PIRC PIROOTS 7371 32 1 = true := by
  quickRfl

theorem ch5182i_tr : trK PIX PIRA PIRB PILAB PITP PITD PIEU PIEV 7371 32 16 = true := by quickRfl

theorem ch5182i_nt : ntK PIX PICA PICB = true := by quickRfl

theorem ch5182i_cl0 : closK PIX PICA PICB PIIMG 7371 0 512 8 = true := by quickRfl
theorem ch5182i_cl1 : closK PIX PICA PICB PIIMG 7371 1 512 8 = true := by quickRfl
theorem ch5182i_cl2 : closK PIX PICA PICB PIIMG 7371 2 512 8 = true := by quickRfl
theorem ch5182i_cl3 : closK PIX PICA PICB PIIMG 7371 3 512 8 = true := by quickRfl
theorem ch5182i_cl4 : closK PIX PICA PICB PIIMG 7371 4 512 8 = true := by quickRfl
theorem ch5182i_cl5 : closK PIX PICA PICB PIIMG 7371 5 512 8 = true := by quickRfl
theorem ch5182i_cl6 : closK PIX PICA PICB PIIMG 7371 6 512 8 = true := by quickRfl
theorem ch5182i_cl7 : closK PIX PICA PICB PIIMG 7371 7 512 8 = true := by quickRfl
theorem ch5182i_cl8 : closK PIX PICA PICB PIIMG 7371 8 512 8 = true := by quickRfl
theorem ch5182i_cl9 : closK PIX PICA PICB PIIMG 7371 9 512 8 = true := by quickRfl
theorem ch5182i_cl10 : closK PIX PICA PICB PIIMG 7371 10 512 8 = true := by quickRfl
theorem ch5182i_cl11 : closK PIX PICA PICB PIIMG 7371 11 512 8 = true := by quickRfl
theorem ch5182i_cl12 : closK PIX PICA PICB PIIMG 7371 12 512 8 = true := by quickRfl
theorem ch5182i_cl13 : closK PIX PICA PICB PIIMG 7371 13 512 8 = true := by quickRfl
theorem ch5182i_cl14 : closK PIX PICA PICB PIIMG 7371 14 512 8 = true := by quickRfl

theorem ch5182i_fo0 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 0 512 8 = true := by
  quickRfl
theorem ch5182i_fo1 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 1 512 8 = true := by
  quickRfl
theorem ch5182i_fo2 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 2 512 8 = true := by
  quickRfl
theorem ch5182i_fo3 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 3 512 8 = true := by
  quickRfl
theorem ch5182i_fo4 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 4 512 8 = true := by
  quickRfl
theorem ch5182i_fo5 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 5 512 8 = true := by
  quickRfl
theorem ch5182i_fo6 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 6 512 8 = true := by
  quickRfl
theorem ch5182i_fo7 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 7 512 8 = true := by
  quickRfl
theorem ch5182i_fo8 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 8 512 8 = true := by
  quickRfl
theorem ch5182i_fo9 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 9 512 8 = true := by
  quickRfl
theorem ch5182i_fo10 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 10 512 8 = true := by
  quickRfl
theorem ch5182i_fo11 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 11 512 8 = true := by
  quickRfl
theorem ch5182i_fo12 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 12 512 8 = true := by
  quickRfl
theorem ch5182i_fo13 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 13 512 8 = true := by
  quickRfl
theorem ch5182i_fo14 : forK PIX PIHA PIHB PILAB PIHP PIHS PIROOTS 7371 10 32 14 512 8 = true := by
  quickRfl

end CFSG.KD.G2Three

end
