data Expr : Type where
    U : Nat -> Expr
    Pi : String -> Expr -> Expr -> Expr
    Lam : String -> Expr -> Expr
    App : Expr -> Expr -> Expr
    Id : String -> Expr
    Sub : Expr -> Expr -> String -> Expr

data Ctx : List (String, Expr) -> Type

data EqCtx : List (String, Expr) -> List (String, Expr) -> Type

data Term : List (String, Expr) -> Expr -> Expr -> Type

data TermEq : List (String, Expr) -> Expr -> Expr -> Expr -> Type

data Var : List (String, Expr) -> Expr -> String -> Type

data Ctx : List (String, Expr) -> Type where
    CtxEmp : Ctx []
    CtxExt : Ctx ctx -> Term ctx (U i) a -> Ctx ((x, a) :: ctx)

infixl 5 `ExtCtx`

data EqCtx : List (String, Expr) -> List (String, Expr) -> Type where
    CtxRefl : EqCtx ctx ctx

data Term : List (String, Expr) -> Expr -> Expr -> Type where
    PiForm :
        Term ctx (U i) a ->
        Term ((x, a) :: ctx) (U i) b ->
        Term ctx (U i) (Pi x a b)
    PiIntro :
        Term ((x, a) :: ctx) b body ->
        Term ctx (Pi x a b) (Lam x body) 
    PiElim :
        Term ctx (Pi x a b) f ->
        Term ctx a arg ->
        Term ctx (Sub b arg x) (App f arg)
    Vble : Ctx ctx -> Var ctx a x -> Term ctx a (Id x)
    Subst1 :
        Term ctx1 tA a ->
        Term (ctx2 ++ (x, tA) :: ctx1) tB b ->
        Term
            (((\(y, tC) => (y, Sub tC a x)) <$> ctx2) ++ ctx1)
            (Sub tB a x)
            (Sub tb a x)
    Wkg1 :
        Term ctx1 (U i) tA ->
        Term (ctx2 ++ ctx1) ty term ->
        Term (ctx2 ++ (x, tA) :: ctx1) ty term

data TermEq : List (String, Expr) -> Expr -> Expr -> Expr -> Type where
    TermRefl : Term ctx a term -> TermEq ctx a term term
    PiComp :
        Term ((x, tA) :: ctx) tB b ->
        Term ctx tA a ->
        TermEq ctx (Sub tB a x) (App (Lam x b) a) (Sub b a x)
    PiUniq :
        Term ctx (Pi x tA tB) f ->
        TermEq ctx (Pi x tA tB) f (Lam x (App f (Id x)))
    Subst2 :
        Term ctx1 tA a ->
        TermEq (ctx2 ++ (x, tA) :: ctx1) tB b c -> 
        TermEq
            (((\(y, tC) => (y, Sub tC a x)) <$> ctx2) ++ ctx1)
            (Sub tB a x)
            (Sub b a x)
            (Sub c a x)
    Subst3 :
        TermEq ctx1 tA a b ->
        Term (ctx2 ++ (x, tA) :: ctx1) tC c ->
        TermEq
            (((\(y, tD) => (y, Sub tD a x)) <$> ctx2) ++ ctx1)
            (Sub tC a x)
            (Sub c a x)
            (Sub c b x)
    Wkg2 :
        Term ctx1 (U i) tA ->
        TermEq (ctx2 ++ ctx1) tB b c ->
        TermEq (ctx2 ++ (x, tA) :: ctx1) tB b c

data Var : List (String, Expr) -> Expr -> String -> Type where
    ZVar : Var ((x, a) :: ctx) a x
    SVar : Var ctx a x -> Var ((y, b) :: ctx) a x