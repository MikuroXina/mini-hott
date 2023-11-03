export type Level = <I>(onZero: I) => (onSucc: (prev: Level) => I) => I;

export const lZero: Level = (onZero) => () => onZero;
export const lSucc =
    (level: Level): Level =>
    () =>
    (onSucc) =>
        onSucc(level);

export const lFromInt = (int: number): Level => (int < 1 ? lZero : lSucc(lFromInt(int - 1)));

export const lEq =
    (left: Level) =>
    (right: Level): boolean =>
        left(right(true)(() => false))((leftPrev) =>
            right(false)((rightPrev) => lEq(leftPrev)(rightPrev)),
        );

export const lMax =
    (left: Level) =>
    (right: Level): Level =>
        left(right)((leftPrev) => right(left)((rightPrev) => lSucc(lMax(leftPrev)(rightPrev))));
