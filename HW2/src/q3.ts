//import {  Exp, isAppExp, isBoolExp, isIfExp, isNumExp, isPrimOp, isProcExp, isVarRef, Program } from "./L31-ast";
//import { Result, makeFailure, makeOk, safe2, mapResult, bind } from "../shared/result";


// script test - 


import { map, zipWith } from "ramda";
import { isLitExp, isLetPlusExp, makeLetPlusExp, isLetExp, makeLetExp, makeBinding, Binding, LetPlusExp, ProcExp, Exp, Program, makeAppExp, makeProcExp, isNumExp, isBoolExp, isPrimOp, isVarRef, isAppExp, CExp, isIfExp, makeIfExp, isProcExp, makeProgram, isDefineExp, makeDefineExp, isProgram, isExp, LetExp, isAtomicExp, isVarDecl, isBinding, isCExp } from "./L31-ast";
import { Result, bind, makeFailure, makeOk, mapResult, safe2 } from "../shared/result";
import { first, rest, isEmpty } from "../shared/list";


/*
Purpose: Transform L31 AST to L3 AST
Signature: l31ToL3(l31AST)
Type: [Exp | Program] => Result<Exp | Program>
*/


export const L31ToL3 = (exp: Exp | Program): Result<Exp | Program> =>
    isProgram(exp) ? bind(mapResult(L31ExpToL3, exp.exps), (exps: Exp[]) => makeOk(makeProgram(exps))) :
    isExp(exp) ? L31ExpToL3(exp) :
    makeFailure("Never");

export const L31ExpToL3 = (exp: Exp): Result<Exp> =>
    isDefineExp(exp) ? bind(L31CExpToL3(exp.val), (val: CExp) => makeOk(makeDefineExp(exp.var, val))) :
    makeOk(allExpToL3(exp));

export const L31CExpToL3 = (exp: CExp): Result<CExp> =>
    isNumExp(exp) ? makeOk(exp) :
    isBoolExp(exp) ? makeOk(exp) :
    isPrimOp(exp) ? makeOk(exp) :
    isVarRef(exp) ? makeOk(exp) :
    isAppExp(exp) ? safe2((rator: CExp, rands: CExp[]) => makeOk(makeAppExp(rator, rands)))
                        (L31CExpToL3(exp.rator), mapResult(L31CExpToL3, exp.rands)) :
    isProcExp(exp) ? bind(mapResult(L31CExpToL3, exp.body), (body: CExp[]) => makeOk(makeProcExp(exp.args, body))) :
    isLetExp(exp) ? safe2((vals : CExp[], body: CExp[]) => makeOk(makeLetExp(zipWith(makeBinding,map(binding => binding.var.var, exp.bindings), vals), body)))
               (mapResult((binding : Binding ) => L31CExpToL3(binding.val), exp.bindings), mapResult(L31CExpToL3,exp.body)) :
    isLetPlusExp(exp) ? safe2((vals : CExp[], body: CExp[]) => makeOk(letPlusToLet(makeLetPlusExp(zipWith(makeBinding,map(binding => binding.var.var, exp.bindings), vals), body))))
    (mapResult((binding : Binding ) => L31CExpToL3(binding.val), exp.bindings), mapResult(L31CExpToL3,exp.body)):
    isLitExp(exp) ? makeOk(exp) :
    isIfExp(exp) ? makeOk(makeIfExp(exp.test, exp.then, exp.alt)) :
    makeFailure(`Unexpected CExp: ${exp.tag}`);


export const letPlusToLet = (exp: LetPlusExp) : LetExp => 
{
        if(exp.bindings.length <= 1)
        {
            return makeLetExp(exp.bindings, exp.body);
        }
        else
        {
            const rewrittenRest = [letPlusToLet(makeLetPlusExp(rest(exp.bindings), exp.body))];
            return makeLetExp([first(exp.bindings)], rewrittenRest);
        }
}

export const allExpToL3 = (cexp: Exp | Program | LetExp | Binding ) :  any | Binding =>
{
    if(isAtomicExp(cexp) || isVarRef(cexp) || isVarDecl(cexp) || isLitExp(cexp)) 
        return cexp;
    else if(isBinding(cexp))
    {
        const rewrittenVal = allExpToL3(cexp.val);
        if(isCExp(rewrittenVal))
        {
            return makeBinding(cexp.var.var,rewrittenVal);
        }
    }
    else if(isDefineExp(cexp))
    {
        const rewrittenVal = allExpToL3(cexp.val);
        if(isCExp(rewrittenVal))
        {
            return makeDefineExp(cexp.var, rewrittenVal);
        }
    }
    if(isAppExp(cexp))
    {
        const rewrittenRator = allExpToL3(cexp.rator);
        if(isCExp(rewrittenRator))
        {
            return makeAppExp(rewrittenRator, map(allExpToL3, cexp.rands));
        }
    }
    else if(isIfExp(cexp))
    {
        const rewrittenTest = allExpToL3(cexp.test);
        const rewrittenThen = allExpToL3(cexp.then);
        const rewrittenAlt = allExpToL3(cexp.alt);
        if(isCExp(rewrittenTest) && isCExp(rewrittenThen) && isCExp(rewrittenAlt))
        {
            return makeIfExp(rewrittenTest,rewrittenThen,rewrittenAlt);
        }
    }
    else if(isProgram(cexp)) return makeProgram(cexp.exps);
    else if(isLetExp(cexp)) return makeLetExp(map(allExpToL3,cexp.bindings), map(allExpToL3,cexp.body));
    else if(isProcExp(cexp)) return makeProcExp(cexp.args, map(allExpToL3,cexp.body));
    else if(isLetPlusExp(cexp)) return letPlusToLet(makeLetPlusExp(map(allExpToL3,cexp.bindings),map(allExpToL3,cexp.body)));

    return cexp;
}