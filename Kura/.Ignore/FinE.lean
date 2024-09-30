import Mathlib.Data.ENat.Basic


def FinE (n : ENat) := match n with
| some n => Fin n
| ⊤ => ℕ

namespace FinE

def toFin {n : ℕ} (a : FinE n) : Fin n := a

def toNat (a : FinE ⊤) : ℕ := a

def ofNat (a : ℕ) : FinE ⊤ := (a : ℕ)

def ofFin {n : Nat} (a : Fin n) : FinE n := a

theorem toNat_ofNat (a : ℕ) : toNat (ofNat a) = a := rfl

theorem toFin_ofFin {n : ℕ} (a : Fin n) : toFin (ofFin a) = a := rfl

theorem ofNat_toNat (a : FinE ⊤) : ofNat (toNat a) = a := rfl

theorem ofFin_toFin {n : ℕ} (a : FinE n) : ofFin (toFin a) = a := rfl

instance instDecEq (n : ENat) : DecidableEq (FinE n) := by
  cases n
  case top => exact Nat.decEq
  case coe n => exact instDecidableEqFin n

end FinE
