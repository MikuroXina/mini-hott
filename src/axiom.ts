import { type Level, lSucc } from "./level.js";
import {
    type Term,
    type Variable,
    eqByDef,
    exists,
    forAll,
    replace,
    universe,
    unwrapExists,
    unwrapForAll,
    unwrapUniverse,
    variable,
} from "./term.js";

export class Sequent extends Map<Variable, Term> {
    equalsTo(other: Map<Variable, Term>): boolean {
        return this.size === other.size && [...this.keys()].every((key) => other.has(key));
    }

    with(key: Variable, value: Term): Sequent {
        const newMap = new Sequent(this);
        newMap.set(key, value);
        return newMap;
    }

    deleted(key: Variable): Sequent {
        const newMap = new Sequent(this);
        newMap.delete(key);
        return newMap;
    }
}

export type IsA = <I>(belong: (what: Term) => (type: Term) => I) => I;
export const isA =
    (what: Term) =>
    (type: Term): IsA =>
    (belong) =>
        belong(what)(type);

export type Judgement = [antecedent: Sequent, consequent: IsA];

export type Infer = (judge: Judgement) => Judgement;

// axioms:

/**
 * ---------------------
 *  ⊢ U(i) : U(succ(i))
 */
export const univIsALargerUniv = (level: Level): Judgement => [
    new Sequent(),
    isA(universe(level))(universe(lSucc(level))),
];

/**
 *     Γ ⊢ A : U(i)
 * --------------------
 *  Γ ⊢ A : U(succ(i))
 */
export const liftUniv: Infer = ([antecedent, consequent]) => {
    const [a, i] = consequent((type) => (univ) => {
        return [type, unwrapUniverse(univ)];
    });
    return [antecedent, isA(a)(universe(lSucc(i)))];
};

/**
 *  Γ ⊢ A : s        x does not appear in Γ
 * -----------------------------------------
 *          Γ, x : A ⊢ x : A
 */
export const start =
    (name: Variable): Infer =>
    ([antecedent, consequent]) => {
        if (antecedent.has(name)) {
            throw new Error(`variable ${name.toString()} was already introduced`);
        }
        const newType = consequent((what) => (type) => {
            unwrapUniverse(type);
            return what;
        });
        return [antecedent.with(name, newType), isA(variable(name))(newType)];
    };

/**
 *  Γ ⊢ C : s        Γ ⊢ a : A
 * ----------------------------
 *       Γ, x : C ⊢ a : A
 */
export const weakening =
    (name: Variable) =>
    (weaker: Judgement): Infer =>
    (judge) => {
        if (!weaker[0].equalsTo(judge[0])) {
            throw new Error("antecedents of two judges must equal");
        }
        const newType = weaker[1]((what) => (type) => {
            unwrapUniverse(type);
            return what;
        });
        return [judge[0].with(name, newType), judge[1]];
    };

/**
 *  Γ ⊢ f : (∀ x : A; B)        Γ ⊢ a : A
 * ---------------------------------------
 *           Γ ⊢ f(a) : B[x := a]
 */
export const application =
    (fn: Judgement): Infer =>
    (param) => {
        if (!fn[0].equalsTo(param[0])) {
            throw new Error("antecedents of two judges must equal");
        }
        const [f, [x, xType, fReturnType]] = fn[1]((what) => (type) => [what, unwrapForAll(type)]);
        const [a, aType] = param[1]((what) => (term) => [what, term]);
        if (!eqByDef(xType)(aType)) {
            throw new Error("parameter types must equal");
        }
        const applied = replace(x)(a)(f);
        const appliedType = replace(x)(a)(fReturnType);
        return [fn[0], isA(applied)(appliedType)];
    };

/**
 *  Γ ⊢ A : s_1        Γ, x : A ⊢ B : s_2
 * ---------------------------------------
 *           Γ ⊢ (∀x : A; B) : s_2
 */
export const product =
    (toPick: Variable) =>
    (toPickIsAType: Judgement): Infer =>
    ([antecedent, consequent]) => {
        const newAntecedent = antecedent.deleted(toPick);
        if (!toPickIsAType[0].equalsTo(newAntecedent)) {
            throw new Error("antecedents of two judges must equal");
        }
        const toPickType = antecedent.get(toPick);
        if (!toPickType) {
            throw new Error("variable to pick was not introduced");
        }
        toPickIsAType[1]((what) => (type) => {
            unwrapUniverse(type);
            if (!eqByDef(what)(toPickType)) {
                throw new Error("`toPickIsAType` was not proving that the term is a type");
            }
        });
        const [newReturnType, univ] = consequent((what) => (type) => [what, type]);
        return [newAntecedent, isA(forAll(toPick)(toPickType)(newReturnType))(univ)];
    };

/**
 *  Γ ⊢ A : s_1        Γ, x : A ⊢ B : s_2        Γ, x : A ⊢ b : B
 * ----------------------------------------------------------------
 *                Γ ⊢ (∃ x : A; b) : (∀ x : A; B)
 */
export const abstraction =
    (target: Variable) =>
    (typeAIsInUniv: Judgement) =>
    (typeBIsInUniv: Judgement): Infer =>
    ([antecedent, consequent]) => {
        if (
            !typeAIsInUniv[0].equalsTo(typeBIsInUniv[0].deleted(target)) ||
            !typeAIsInUniv[0].equalsTo(antecedent.deleted(target))
        ) {
            throw new Error("antecedents of three judges must equal");
        }
        const typeA = typeAIsInUniv[1]((type) => (univ) => {
            unwrapUniverse(univ);
            return type;
        });
        const typeB = typeBIsInUniv[1]((type) => (univ) => {
            unwrapUniverse(univ);
            return type;
        });
        const valueB = consequent((what) => (type) => {
            if (!eqByDef(typeB)(type)) {
                throw new Error("type of consequent must equals to `typeB`");
            }
            return what;
        });
        return [typeAIsInUniv[0], isA(exists(target)(typeA)(valueB))(forAll(target)(typeA)(typeB))];
    };

export type BetaReduce = (from: Term) => Term;
export const betaCompose =
    (left: BetaReduce) =>
    (right: BetaReduce): BetaReduce =>
    (from) =>
        left(right(from));

/**
 * ---------------------------------
 *  (∃ x : A; B)(C) →_β B[x := C]
 */
export const betaApplication: BetaReduce = (from) => {
    const appExpected = () => {
        throw new Error("expected app");
    };
    const [aToB, c] = from<() => [Term, Term]>(appExpected)(appExpected)((fn) => (param) => () => [
        fn,
        param,
    ])(appExpected)(appExpected)();
    const [x, , b] = unwrapExists(aToB);
    return replace(x)(c)(b);
};

/**
 *            B →_β B'
 * -------------------------------
 *  ∃ x : A; B →_β ∃ x : A; B'
 */
export const betaMapExistsReturnValue =
    (valueMapper: BetaReduce): BetaReduce =>
    (from) => {
        const [x, a, b] = unwrapExists(from);
        return exists(x)(a)(valueMapper(b));
    };

/**
 *            A →_β A'
 * -------------------------------
 *  ∃ x : A; B →_β ∃ x : A'; B
 */
export const betaMapExistsNameType =
    (typeMapper: BetaReduce): BetaReduce =>
    (from) => {
        const [x, a, b] = unwrapExists(from);
        return exists(x)(typeMapper(a))(b);
    };

/**
 *            B →_β B'
 * -------------------------------
 *  ∀ x : A; B →_β ∀ x : A; B'
 */
export const betaMapForAllReturnType =
    (typeMapper: BetaReduce): BetaReduce =>
    (from) => {
        const [x, a, b] = unwrapForAll(from);
        return forAll(x)(a)(typeMapper(b));
    };

/**
 *            A →_β A'
 * -------------------------------
 *  ∀ x : A; B →_β ∀ x : A'; B
 */
export const betaMapForAllNameType =
    (typeMapper: BetaReduce): BetaReduce =>
    (from) => {
        const [x, a, b] = unwrapForAll(from);
        return forAll(x)(typeMapper(a))(b);
    };

/**
 *  Γ ⊢ B : s_1        A =_β B        Γ ⊢ a : A
 * -----------------------------------------------
 *                  Γ ⊢ a : B
 */
export const conversion =
    (typeBIsInUniv: Judgement) =>
    (aIsB: BetaReduce): Infer =>
    ([antecedent, consequent]) => {
        if (!typeBIsInUniv[0].equalsTo(antecedent)) {
            throw new Error("antecedents of two judges must equal");
        }
        const typeB = typeBIsInUniv[1]((type) => (univ) => {
            unwrapUniverse(univ);
            return type;
        });
        const a = consequent((what) => (type) => {
            if (!eqByDef(aIsB(type))(typeB)) {
                throw new Error("reduced type did not match");
            }
            return what;
        });
        return [antecedent, isA(a)(typeB)];
    };
