import { Exp, isExp, isLitExp, isStrExp, Program } from '../imp/L3-ast';
import { Result, makeFailure } from '../shared/result';

import { map } from "ramda";
import { isProgram, isBoolExp, isNumExp, isVarRef, isPrimOp, isProcExp, isIfExp, isAppExp, isDefineExp, PrimOp, CExp } from '../imp/L3-ast';
import { makeOk, bind, mapResult, safe2 } from '../shared/result';
import { Binding, isBinding, isCExp, isLetExp } from './L31-ast';
import { isStringLiteral } from 'typescript';
import exp from 'constants';
import { isSExp, isSymbolSExp, SExpValue } from '../imp/L3-value';


/*
Purpose: Transform L3 AST to JavaScript program string
Signature: l30ToJS(l2AST)
Type: [EXP | Program] => Result<string>
*/
export const l30ToJS = (exp: Exp | Program): Result<string>  => 
    isProgram(exp) ? bind(mapResult(l30ToJS, exp.exps), exps => makeOk(exps.join(";\n"))) :
    isBoolExp(exp) ? makeOk(exp.val ? 'True' : 'False') :
    isNumExp(exp) ? makeOk(exp.val.toString()) :
    isVarRef(exp) ? makeOk(exp.var) :
    isDefineExp(exp) ? bind(l30ToJS(exp.val), val => makeOk(`const ${exp.var.var} = ${val}`)) :
    isIfExp(exp) ? bind(l30ToJS(exp.test), test  => makeOk(`(${test} ? ${(l30ToStr(exp.then))} : ${(l30ToStr(exp.alt))})`)) :
    isPrimOp(exp) ? makeOk(convertPrimOp(exp.op)) :
    isProcExp(exp) ? bind(l30ToJS(exp.body[exp.body.length-1]), body => makeOk("((" +  
    map((p) => p.var, exp.args).join(",") + ") => " + body + ")")) :
    isAppExp(exp) ?  
        (
        isPrimOp(exp.rator) ? makeOk(primOpApp2Java(exp.rator, exp.rands)) :
        safe2((rator: string, rands: string[]) => makeOk(`${rator}(${rands.join(",")})`))
            (l30ToJS(exp.rator), mapResult(l30ToJS, exp.rands))
        ) :
    isLetExp(exp) ?  makeOk( "((" + exp.bindings.map(bindingsVarsToStr).join(",") +") => " + exp.body.map(l30ToStr).toString() + ")(" + exp.bindings.map(bindingsValsToStr).join(",") +")") :
    isLitExp(exp) ? makeOk(`Symbol.for("${isSymbolSExp(exp.val) ? exp.val.val : 
        "Not symbolExp"}")`) :
    isStrExp(exp) ? makeOk("\"" + exp.val  +"\"") :
    makeFailure("Never");

const convertPrimOp = (op : string) : string =>
    op === "number?" ? "((x) => (typeof(x) === int) or (x) => (typeof(x) === double))" :
    op === "boolean?" ? "((x) => (typeof(x) === boolean))" :
    op === "symbol?" ? "((x) => (typeof (x) === symbol))" :
    op === "string?" ? "((x) => (typeof (x) === string))" :
    op;

const bindingsVarsToStr = (binding : Binding) : string =>
    binding.var.var;


const bindingsValsToStr = (binding : Binding) : string =>
    isNumExp(binding.val) ? binding.val.val.toString() :
    isVarRef(binding.val) ? binding.val.var :
    "";

const l30ToStr = (exp: Exp | Program | CExp | Binding): string  =>
    isNumExp(exp) ? exp.val.toString() :
    isVarRef(exp) ? exp.var :
    isStrExp(exp) ? "\"" + exp.val  +"\"" :
    isDefineExp(exp) ? `${exp.var.var} = ${exp.val}` :
    isAppExp(exp) ?  
        (
        isPrimOp(exp.rator) ? primOpApp2Java(exp.rator, exp.rands) :
        `${l30ToStr(exp.rator)}(${exp.rands.map(l30ToStr).join(",")})`) :
    "";

const primOpApp2Java = (rator : PrimOp, rands : CExp[]) : string => 
    rator.op === "not" ? "(!" + l30ToStr(rands[0]) + ")" :
    rator.op === "number?" || rator.op === "boolean?" ? `${convertPrimOp(rator.op)}(${l30ToStr(rands[0])})` :
    rator.op === ">" || rator.op === "<" || rator.op === "==" || rator.op === "!=" ? "("+rands.map(l30ToStr).join(" " + rator.op + " ") + ")" :  
    rator.op === "=" || rator.op === "eq?" ? "("+rands.map(l30ToStr).join(" === ") + ")" : 
    rator.op === "string=?" ? "("+rands.map(l30ToStr).join(" === ") + ")" :
    
    "(" + rands.map(l30ToStr).join(" " + convertPrimOp(rator.op) + " ") + ")";
