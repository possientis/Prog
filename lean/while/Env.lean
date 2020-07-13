def Env  : Type := string → ℕ

def env : list (string × ℕ) → Env
| []        := λ s, 0
| ((v,n) :: xs) := λ s, if s = v then n else env xs s


