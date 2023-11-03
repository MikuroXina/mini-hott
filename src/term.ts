import { type Level, lEq } from "./level.js";

export type Variable = symbol;

export type Term = <I>(
    onUniverse: (level: Level) => I,
) => (
    onVar: (name: Variable) => I,
) => (
    onApp: (fn: Term) => (param: Term) => I,
) => (
    onExists: (name: Variable) => (nameType: Term) => (returnValue: Term) => I,
) => (onForAll: (name: Variable) => (nameType: Term) => (returnType: Term) => I) => I;
export const universe =
    (level: Level): Term =>
    (onUniverse) =>
    () =>
    () =>
    () =>
    () =>
        onUniverse(level);
export const variable =
    (name: Variable): Term =>
    () =>
    (onVar) =>
    () =>
    () =>
    () =>
        onVar(name);
export const app =
    (fn: Term) =>
    (param: Term): Term =>
    () =>
    () =>
    (onApp) =>
    () =>
    () =>
        onApp(fn)(param);
export const exists =
    (name: Variable) =>
    (nameType: Term) =>
    (returnValue: Term): Term =>
    () =>
    () =>
    () =>
    (onExists) =>
    () =>
        onExists(name)(nameType)(returnValue);
export const forAll =
    (name: Variable) =>
    (nameType: Term) =>
    (returnType: Term): Term =>
    () =>
    () =>
    () =>
    () =>
    (onForAll) =>
        onForAll(name)(nameType)(returnType);

export const unwrapUniverse = (term: Term): Level => {
    const universeExpected = () => {
        throw new Error("expected universe");
    };
    return term((level) => level)(universeExpected)(universeExpected)(universeExpected)(
        universeExpected,
    );
};
export const unwrapExists = (term: Term): [name: Variable, nameType: Term, returnValue: Term] => {
    const existsExpected = () => {
        throw new Error("expected exists");
    };
    return term<() => [Variable, Term, Term]>(existsExpected)(existsExpected)(existsExpected)(
        (name) => (nameType) => (returnValue) => () => [name, nameType, returnValue],
    )(existsExpected)();
};
export const unwrapForAll = (term: Term): [name: Variable, nameType: Term, returnType: Term] => {
    const forAllExpected = () => {
        throw new Error("expected for all");
    };
    return term<() => [Variable, Term, Term]>(forAllExpected)(forAllExpected)(forAllExpected)(
        (name) => (nameType) => (returnType) => () => [name, nameType, returnType],
    )(forAllExpected)();
};

export const eqByDef =
    (left: Term) =>
    (right: Term): boolean =>
        left((leftLevel) =>
            right((rightLevel) => lEq(leftLevel)(rightLevel))(() => false)(() => () => false)(
                () => () => () => false,
            )(() => () => () => false),
        )((leftName) =>
            right(() => false)((rightName) => leftName === rightName)(() => () => false)(
                () => () => () => false,
            )(() => () => () => false),
        )(
            (leftFn) => (leftParam) =>
                right(() => false)(() => false)(
                    (rightFn) => (rightParam) =>
                        eqByDef(leftFn)(rightFn) && eqByDef(leftParam)(rightParam),
                )(() => () => () => false)(() => () => () => false),
        )(
            (leftName) => (leftNameType) => (leftReturnValue) =>
                right(() => false)(() => false)(() => () => false)(
                    (rightName) => (rightNameType) => (rightReturnValue) =>
                        leftName === rightName &&
                        eqByDef(leftNameType)(rightNameType) &&
                        eqByDef(leftReturnValue)(rightReturnValue),
                )(() => () => () => false),
        )(
            (leftName) => (leftNameType) => (leftReturnType) =>
                right(() => false)(() => false)(() => () => false)(() => () => () => false)(
                    (rightName) => (rightNameType) => (rightReturnType) =>
                        leftName === rightName &&
                        eqByDef(leftNameType)(rightNameType) &&
                        eqByDef(leftReturnType)(rightReturnType),
                ),
        );

export const replace =
    (target: Variable) =>
    (into: Term) =>
    (source: Term): Term =>
        source(() => source)((name) => (name === target ? into : source))(
            (fn) => (param) => app(replace(target)(into)(fn))(replace(target)(into)(param)),
        )(
            (name) => (nameType) => (returnType) =>
                name === target
                    ? exists(name)(nameType)(returnType)
                    : exists(name)(replace(target)(into)(nameType))(
                          replace(target)(into)(returnType),
                      ),
        )(
            (name) => (nameType) => (returnType) =>
                name === target
                    ? forAll(name)(nameType)(returnType)
                    : forAll(name)(replace(target)(into)(nameType))(
                          replace(target)(into)(returnType),
                      ),
        );
