import { type Def, def } from "./axiom.js";
import { lMax } from "./level.js";
import {
    app,
    eqByDef,
    exists,
    forAll,
    universe,
    unwrapExists,
    unwrapForAll,
    unwrapUniverse,
    variable,
} from "./term.js";

export const fnType =
    (from: Def) =>
    (to: Def): Def => {
        const [fromType, fromUniv] = from((type) => (univ) => [type, unwrapUniverse(univ)]);
        const [toType, toUniv] = to((type) => (univ) => [type, unwrapUniverse(univ)]);
        return def(forAll(Symbol("x"))(fromType)(toType))(universe(lMax(fromUniv)(toUniv)));
    };

export const identityFn = (type: Def): Def => fnType(type)(type);

export const composeFn =
    (left: Def) =>
    (right: Def): Def => {
        const [leftFn, [, leftFrom, leftTo]] = left((what) => (type) => [what, unwrapForAll(type)]);
        const [rightFn, [param, rightFrom, rightTo]] = right((what) => (type) => [
            what,
            unwrapForAll(type),
        ]);
        if (!eqByDef(leftFrom)(rightTo)) {
            throw new Error("cannot compose two functions");
        }
        return def(exists(param)(rightFrom)(app(leftFn)(app(rightFn)(variable(param)))))(
            forAll(Symbol("x"))(rightFrom)(leftTo),
        );
    };

/**
 *  (λ x : A; λ y : B; z) : (∀ x : A; ∀ y : B; C)
 * -------------------------------------------------
 *  (λ y : B; λ x : A; z) : (∀ y : B; ∀ x : A; C)
 */
export const swapFn = (f: Def): Def => {
    const [xToYToZ, [, a, bToC]] = f((what) => (type) => [what, unwrapForAll(type)]);
    const [, b, c] = unwrapForAll(bToC);
    const [x, typeX, yToZ] = unwrapExists(xToYToZ);
    if (!eqByDef(typeX)(a)) {
        throw new Error("inconsistent parameter type");
    }
    const [y, typeY, z] = unwrapExists(yToZ);
    if (!eqByDef(typeY)(b)) {
        throw new Error("inconsistent parameter type");
    }
    return def(exists(y)(b)(exists(x)(a)(z)))(forAll(y)(b)(forAll(x)(a)(c)));
};
