import Mathlib.Topology.Basic

inductive Cmd (t : Type u) (a : Type v) where
  | skip : Cmd t a
  | seq : Cmd t a → Cmd t a → Cmd t a
  | par : Cmd t a → Cmd t a → Cmd t a
  | ifstmt : t → Cmd t a → Cmd t a → Cmd t a
  | while  : t → Cmd t a → Cmd t a
  | act : a → Cmd t a

def Node := ℕ

