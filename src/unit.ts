import { type Def, def } from "./axiom.js";
import { lZero } from "./level.js";
import { universe, variable } from "./term.js";

export const unit: Def = def(variable(Symbol("*")))(universe(lZero));
