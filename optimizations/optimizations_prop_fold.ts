import { setMaxListeners } from "events";
import { start } from "repl";
import { Parameter, Type } from "../ast";
import { BasicBlock, Expr, FunDef, Program, Stmt, Value, VarInit } from "../ir";
import { tcStmt } from "../type-check";
import { Env, generateEnvironmentFunctions, generateEnvironmentProgram, generateEnvironmentProgramForLiveness } from "./optimization_common";
import { checkIfFoldableBinOp, checkPropagateValEquality, checkStmtEquality, checkValueEquality, duplicateEnv, evaluateBinOp, evaluateUniOp, isTagBigInt, isTagNumber } from "./optimization_utils";


export type propagateVal = {
    tag: "nac" | "val" | "undef", value?: Value<any>;
}

export class constPropEnv extends Env {
    vars: Map<string, propagateVal>;

    constructor(vars: Map<string, propagateVal>) {
        super()
        this.vars = vars;
    }

    get(arg: string): propagateVal {
        if (!this.vars.has(arg)) return {tag: "nac"};
        return this.vars.get(arg);
    }

    set(arg: string, value: propagateVal) {
        this.vars.set(arg, value);
    }

    has(arg: string): boolean {
        return this.vars.has(arg);
    }

    duplicateEnv(): constPropEnv {
        return new constPropEnv(new Map(this.vars));
    }

    checkEqual(b: constPropEnv): boolean {
        const aVars = this.vars;
        const bVars = b.vars;

        for (const key of aVars.keys()) {
            const aValue = aVars.get(key);
            const bValue = bVars.get(key);

            if (!checkPropagateValEquality(aValue, bValue)) return false;
        }
        return true;
    }

    updateEnvironmentByBlock(block: BasicBlock<any>): constPropEnv {
        var outEnv: constPropEnv = new constPropEnv(new Map(this.vars));
        block.stmts.forEach(statement => {
            if (statement === undefined) { console.log(block.stmts); }
            switch(statement.tag){
                case "assign":
                    const optimizedExpression = optimizeExpression(statement.value, outEnv);
                    if (optimizedExpression.tag === "value") {
                        if (optimizedExpression.value.tag === "id") {
                            outEnv.vars.set(statement.name, { tag: "nac" });
                        }
                        else {
                            outEnv.vars.set(statement.name, { tag: "val", value: optimizedExpression.value });
                        }
                    }
                    else {
                        outEnv.vars.set(statement.name, { tag: "nac" });
                    }
                    break;
                case "store":
                    const optimizedStart = optimizeValue(statement.start, outEnv);
                    const optimizedOffset = optimizeValue(statement.offset, outEnv);
                    const optimizedValue = optimizeValue(statement.value, outEnv);
                    if (optimizedStart.tag !== "id" || optimizedOffset.tag === "id" || optimizedOffset.tag === "none")
                        break;
                    const generatedVarName = optimizedStart.name + "$$" + optimizedOffset.value.toString();
                    if (statement.value.tag === "id"){
                        outEnv.vars.set(generatedVarName, {tag: "nac"});
                    }
                    outEnv.vars.set(generatedVarName, {tag: "val", value: optimizedValue});
                    break;
                default:
                    break;
            }
        });
        return outEnv;
    }

    mergeEnvironment(b: constPropEnv): constPropEnv {
        var returnEnv: constPropEnv = new constPropEnv(new Map<string, propagateVal>());
        this.vars.forEach((aValue: propagateVal, key: string) => {
            var bValue: propagateVal = b.vars.get(key);

            if (bValue === undefined) bValue = {tag: "undef"};

            if (bValue.tag === "nac" || aValue.tag === "nac")
                returnEnv.vars.set(key, { tag: "nac" });
            else if (aValue.tag === "undef" && bValue.tag === "undef") {
                returnEnv.vars.set(key, { tag: "undef" })
            }
            else if (aValue.tag === "undef") {
                returnEnv.vars.set(key, { tag: "val", value: bValue.value })
            }
            else if (bValue.tag === "undef") {
                returnEnv.vars.set(key, { tag: "val", value: aValue.value });
            }
            else if (checkValueEquality(aValue.value, bValue.value))
                returnEnv.vars.set(key, { tag: "val", value: aValue.value });
            else
                returnEnv.vars.set(key, { tag: "nac" });
        });
        return returnEnv;
    }
}


function optimizeValue(val: Value<any>, env: Env): Value<any>{
    if (val.tag !== "id"){
        return val;
    }
    if (env.has(val.name)){
        if (["nac", "undef"].includes(env.get(val.name).tag))
            return val;
        
        val = env.get(val.name).value;
    }
    return val;
}

export function compareIndexVLength(indexValue: BigInt, lengthValue: BigInt): boolean{
    if (indexValue < 0n || indexValue >= lengthValue)
        return false;
    return true;
}

export function shouldOptimizeBoundCheck(expr: Expr<any>, env: Env): boolean{
    if (expr.tag !== "call" || expr.name !== "check_index_out_of_bounds")
        throw new Error("Compiler Error - Method meant to optimize Bound checking expressions");
    var indexValue: BigInt;
    var lengthValue: BigInt;
    const optimizedArguments: Array<Value<any>> = expr.arguments.map(a => {
        return optimizeValue(a, env);
    });
    switch(optimizedArguments[0].tag){
        case "wasmint":
            lengthValue = BigInt(optimizedArguments[0].value);
            switch(optimizedArguments[1].tag){
                case "wasmint":
                    indexValue = BigInt(optimizedArguments[1].value);
                    break;
                case "num":
                    indexValue = BigInt(optimizedArguments[1].value);
                    break;
                default:
                    return false;
            }
            break;
        case "num":
            lengthValue = BigInt(optimizedArguments[0].value);
            switch(optimizedArguments[1].tag){
                case "wasmint":
                    indexValue = BigInt(optimizedArguments[1].value);
                    break;
                case "num":
                    indexValue = BigInt(optimizedArguments[1].value);
                    break;
                default:
                    return false;
            }
            break;
        default:
            return false;
    }
    return compareIndexVLength(indexValue, lengthValue);
}

export function shouldOptimizeBoundCheckStmt(stmt: Stmt<any>, env: Env): boolean{
    if (stmt.tag !== "expr" || stmt.expr.tag !== "call" || stmt.expr.name !== "check_index_out_of_bounds")
        throw new Error("Compiler Error - Method meant to optimize Bound checking statements");
    return shouldOptimizeBoundCheck(stmt.expr, env);
}

function optimizeExpression(e: Expr<any>, env: Env): Expr<any> {
    switch(e.tag) {
        case "value":
           var optimizedValue: Value<any> = optimizeValue(e.value, env);
           return {...e, value: optimizedValue};
        case "binop":
            var left = optimizeValue(e.left, env);
            var right = optimizeValue(e.right, env);
            if (left.tag === "id" || right.tag === "id" || !checkIfFoldableBinOp(e.op, left, right))
                return {...e, left: left, right: right};
            var val: Value<any> = evaluateBinOp(e.op, left, right);
            return {tag: "value", value: val};
        case "uniop":
            var arg = optimizeValue(e.expr, env);
            if (arg.tag === "id")
                return {...e, expr: arg};
            var val: Value<any> = evaluateUniOp(e.op, arg);
            return {tag: "value", value: val};
        case "builtin1":
            var arg = optimizeValue(e.arg, env);
            return {...e, arg: arg};
        case "builtin2":
            var left = optimizeValue(e.left, env);
            var right = optimizeValue(e.right, env);
            return {...e, left:left, right: right};
        case "call":
            var modifiedParams = e.arguments.map(a => {
                return optimizeValue(a, env);
            });
            return {...e, arguments: modifiedParams};
        case "alloc":
            var amount = optimizeValue(e.amount, env);
            return {...e, amount: amount};
        case "load":
            var optimizedStart = optimizeValue(e.start, env);
            var optimizedOffset = optimizeValue(e.offset, env);
            if (optimizedStart.tag !== "id" || optimizedOffset.tag === "id" || optimizedOffset.tag === "none" || !env.has(optimizedStart.name) || (env.get(optimizedStart.name).tag === "nac"))
                return {...e, start: optimizedStart, offset: optimizedOffset};
            const generatedVarName = optimizedStart.name + "$$" + optimizedOffset.value.toString();
            const envValue = env.get(generatedVarName);
            if (envValue.tag !== "val")
                return {...e, start: optimizedStart, offset: optimizedOffset};
            if (["num", "wasmint"].includes(envValue.value.tag)) envValue.value = {a: e.a, tag: "num", value: BigInt(envValue.value.value)};
            return {a: e.a, tag: "value", value: envValue.value};
        default:
            return e;
    }
}

function optimizeStatements(stmt: Stmt<any>, env: Env): Stmt<any>{
    switch(stmt.tag){
        case "assign":
            var optimizedExpression: Expr<any> = optimizeExpression(stmt.value, env);
            if (optimizedExpression.tag === "value"){
                if (optimizedExpression.value.tag === "id"){
                    env.set(stmt.name, {tag: "nac"});
                }
                else{
                    env.set(stmt.name, {tag: "val", value: optimizedExpression.value});
                }
            }
            else{
                env.set(stmt.name, {tag: "nac"});
            }
            return {...stmt, value: optimizedExpression};
        case "return":
            var optimizedValue: Value<any> = optimizeValue(stmt.value, env);
            return {...stmt, value: optimizedValue};
        case "expr":
            if (stmt.expr.tag === "call" && stmt.expr.name === "check_index_out_of_bounds" && shouldOptimizeBoundCheckStmt(stmt, env)) return {tag: "pass"};
            var optimizedExpression: Expr<any> = optimizeExpression(stmt.expr, env);
            return {...stmt, expr: optimizedExpression};
        case "pass":
            return stmt;
        case "ifjmp":
            var optimizedValue: Value<any> = optimizeValue(stmt.cond, env);
            return {...stmt, cond: optimizedValue};
        case "jmp":
            return stmt;
        case "store":
            var optimizedStart = optimizeValue(stmt.start, env);
            var optimizedOffset = optimizeValue(stmt.offset, env);
            var optimizedValue = optimizeValue(stmt.value, env);
            if (optimizedStart.tag !== "id" || optimizedOffset.tag === "id" || optimizedOffset.tag === "none" || !env.has(optimizedStart.name) || (env.get(optimizedStart.name).tag === "nac"))
                return stmt;
            const generatedVarName = optimizedStart.name + "$$" + optimizedOffset.value.toString();
            if (stmt.value.tag === "id"){
                env.set(generatedVarName, {tag: "nac"});
            }
            env.set(generatedVarName, {tag: "val", value: optimizedValue});
            return stmt;
        default:
            return stmt;
    }
}

function optimizeBlock(block: BasicBlock<any>, env: Env): [BasicBlock<any>, boolean]{
    var blockOptimized: boolean = false;
    var newStmts: Stmt<any>[] = block.stmts.map(s => {
        var optimizedstatement = optimizeStatements(s, env);
        if (!blockOptimized && !checkStmtEquality(optimizedstatement, s)) {
            blockOptimized = true;
        }
        return optimizedstatement;
    });
    return [{...block, stmts: newStmts}, blockOptimized];
}

function computeInitEnv(varDefs: Array<VarInit<any>>, dummyEnv: boolean): Env {
    var env: Env = new constPropEnv(new Map<string, propagateVal>());
    varDefs.forEach(def => {

        //To not propagate any value if the type is a class (Certain variable initializations when converted
        //to lower take type undefined)
        if (def.type !== undefined && def.type.tag === "class") env.set(def.name, {tag: "nac"});

        if (!dummyEnv)
            env.set(def.name, { tag: "val", value: def.value });
        else
            env.set(def.name, { tag: "undef" });
    });
    return env;
}

function addParamsToEnv(params: Array<Parameter<any>>, env: constPropEnv, dummyEnv: boolean) {
    params.forEach(p => {
        if (dummyEnv) {
            env.set(p.name, { tag: "undef" });
        }
        else {
            env.set(p.name, { tag: "nac" });
        }
    });
}

export function constantPropagateAndFoldProgramBody(program: Program<any>): [Program<any>, boolean] {
    if (program.body.length == 0) return [program, false];
    var [inEnvMapping, _outEnvMapping]: [Map<string, Env>, Map<string, Env>] = generateEnvironmentProgram(program, computeInitEnv);

    //Write code to optimize the program using the environment
    var programOptimized: boolean = false;
    var newBody: Array<BasicBlock<any>> = program.body.map(b => {
        var tempBlockEnv: Env = duplicateEnv(inEnvMapping.get(b.label));
        var [optimizedBlock, blockOptimized]: [BasicBlock<any>, boolean] = optimizeBlock(b, tempBlockEnv);
        if (!programOptimized && blockOptimized) programOptimized = true;
        return optimizedBlock;
    });
    return [{ ...program, body: newBody }, programOptimized]
}

export function constantPropagateAndFoldProgramFuns(func: FunDef<any>): [FunDef<any>, boolean] {
    if (func.body.length === 0) return [func, false];
    var [inEnvMapping, _outEnvMapping]: [Map<string, Env>, Map<string, Env>] = generateEnvironmentFunctions(func, computeInitEnv, addParamsToEnv);

    var functionOptimized: boolean = false;
    var newBody: Array<BasicBlock<any>> = func.body.map(b => {
        var tempBlockEnv: Env = duplicateEnv(inEnvMapping.get(b.label));
        var [optimizedBlock, blockOptimized]: [BasicBlock<any>, boolean] = optimizeBlock(b, tempBlockEnv);
        if (!functionOptimized && blockOptimized) functionOptimized = true;
        return optimizedBlock;
    });

    return [{ ...func, body: newBody }, functionOptimized];
}
