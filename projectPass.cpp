
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopInfoImpl.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include "llvm/ADT/ValueMap.h"
#include <ostream>
#include <string>
#include <stdlib.h>
#include <stdio.h>

using namespace llvm;

#define D(v) (DEBUG(errs() << v))
#define DT(type,v) (DEBUG_WITH_TYPE(type,errs() << v))
#define max(a,b) (a>b?a:b)

namespace {

	typedef std::pair<char*,int> arrelem;
	typedef std::pair<Value*,Value*> arrIndex;

	class triplet
	{
		public: 
			Value *a;
			Value *b;
			int op;
			triplet()
			{
				a = b = NULL;
				op = -1;
			}
	};

	class Node
	{
		public:
			arrelem e;
			std::vector<Node*> parents;
			//Node *parent;
			std::vector<Node*> children;
			bool visited;
			Node()
			{
				visited = false;
			}
	};

	class IndexVariable 
	{
		public: 
			Value *start;
			Value *end;
			Value *inc;
			int level;
			int sign;
			IndexVariable()
			{
				start = end = inc = NULL;
				level = -1;
				sign = 0;
			}
			friend inline raw_ostream &operator<<(raw_ostream &os, const IndexVariable &iv);
	};

	inline raw_ostream &operator<<(raw_ostream &os, const IndexVariable &iv)
	{
		if(iv.start)
			os << *iv.start;
		else
			os << "null";
		os << ",,";
		if(iv.end)
			os << *iv.end;
		else
			os << "null";
		os << ",,";
		if(iv.inc)
		{
			os << *iv.inc;
			if(iv.sign < 0)
				os << "(negative)";
		}
		else
			os << "null";
		os << ",,";
		os << iv.level;
		//os << ",," << iv.sign;
		//os << "IndexVariable: " << (iv.start ? *iv.start : "null") << ",," << (iv.end ? *iv.end : "null") << ",," << (iv.inc ? *iv.inc : "null") << ",," << iv.level << "\n"; 
		return os;
	}

	inline raw_ostream &operator<<(raw_ostream &os, const triplet &t)
	{
		if(t.a)
			os << *t.a;
		else
			os << "null";
		os << ",,";
		if(t.b)
			os << *t.b;
		else
			os << "null";
		os << ",,";
		os << t.op;
		return os;
	}

	struct ProjectPass : public LoopPass {

		static char ID;
		std::map<std::string,Node*> depTree;
		std::map<Value *, Value *> loaded;
		std::map<Value *, triplet> cmpInsts;
		std::vector<Value *> branchList;
		std::map<Value *, triplet> binaryOps;
		std::map<Value *, IndexVariable> indexVars; 
		std::map<Value *, IndexVariable> candidateVars;

		ProjectPass() : LoopPass(ID)
		{

		}

		virtual bool doFinalization()
		{
			return false;
		}

		virtual bool runOnLoop(Loop *l, LPPassManager &lp) 
		{

			std::vector<BasicBlock*> blist = l->getBlocks();
			std::vector<Instruction*> storeInsts;
			//DEBUG_WITH_TYPE("loop", errs() << *l << "\n");
			//Value *indvar;
			//IndexVariable *iv = getIV(l,indvar);
			for(std::vector<BasicBlock*>::iterator it = blist.begin(); it != blist.end(); it++)
			{
				for(BasicBlock::iterator inst = (*it)->begin(); inst != (*it)->end(); inst++)
				{
					DEBUG_WITH_TYPE("main", errs() << *inst << "\n");
					Value *v = inst;
					triplet binOp;
					binOp.op = inst->getOpcode();
					binOp.a = inst->getOperand(0);
					if(inst->getNumOperands() >= 2)
						binOp.b = inst->getOperand(1);
					IndexVariable indVar;
					
					if(inst->getOpcode() == Instruction::Add || inst->getOpcode() == Instruction::Sub)
					{
						//DEBUG(errs() << "constant: " << constantValueInUse(v) << " same: " << similarValueInUse(v) << "\n");
						binaryOps.insert(std::pair<Value *,triplet>(v,binOp));
						if(Value *sv = similarValueInUse(v))
						{
							Value *constValue = constantValueInUse(v);
							if(constValue)
							{
								indVar.inc = constValue;
								indexVars.insert(std::pair<Value *, IndexVariable>(v,indVar));
							}
							else
							{
								Value *ov = (sv == inst->getOperand(0) ? inst->getOperand(1) : inst->getOperand(0));
								indVar.inc = ov;
								candidateVars.insert(std::pair<Value *, IndexVariable>(v,indVar));
							}
						}
					}
					else if(inst->getOpcode() == Instruction::Load)
					{
						DEBUG_WITH_TYPE("main", errs() << "Load Instruction\n");
						loaded[inst] = inst->getOperand(0);
					}
					else if(inst->getOpcode() == Instruction::Store)
					{
						DEBUG_WITH_TYPE("main", errs() << "Store Inst: " << *inst << "\n");
						Value *op0 = inst->getOperand(0);
						Value *op1 = inst->getOperand(1);
						std::vector<arrIndex*> rhs,lhs;
						parseValue(op0,&rhs);
						DEBUG_WITH_TYPE("main", errs() << "After parse: Size: " << lhs.size() << "\n");
						parseValue(op1,&lhs);
						DEBUG_WITH_TYPE("main", errs() << "After parse: Size: " << rhs.size() << "\n");
						if(lhs.size() == 0 && rhs.size() == 0)
						{
							DEBUG_WITH_TYPE("main", errs() << "Normal assignment instruction\n");
							DEBUG(errs() << "Store Instruction: No of Operands = " << inst->getNumOperands() << "\n");
							Value *indName = inst->getOperand(1);
							IndexVariable indVar;
							//indVar.level = l->
							Instruction *binInst = dyn_cast<Instruction>(inst->getOperand(0));
							if(binInst)
							{
								DEBUG(errs() << "op instruction: " << *binInst << "\n");
								if(Value *inc = getIncrement(binInst, indName))
								{
									indVar.inc = inc;
									if(binInst->getOpcode() == Instruction::Sub)
										indVar.sign = -1;
									else
										indVar.sign = 1;
									updateIndexVar(indName, indVar);
									DEBUG(errs() << "Found index Variable: " << indVar << "\n");
									//indexVars[indName] = indVar;
								}
							}
							else
							{
								//a constant which means that variable is being initialised..
								indVar.start = inst->getOperand(0);
								updateIndexVar(indName, indVar);
								DEBUG(errs() << "Found index Variable: " << indVar << "\n");
							}
						}
						else
						{
							DEBUG_WITH_TYPE("main", errs() << "Not a normal assignment. To be possibly considered for SIMD calculation..\n");
							storeInsts.push_back(inst);
						}
						lhs.clear();
						rhs.clear();
					}
					else if(inst->getOpcode() == Instruction::Br)
					{
						if(inst->getNumOperands() >= 2)
						{
							DEBUG(errs() << *inst->getOperand(0) << ",," << *inst->getOperand(1) << "\n");
							branchList.push_back(inst->getOperand(0));
						}
					}
					else if(inst->getOpcode() == Instruction::ICmp)
					{
						CmpInst *cmpInst = dyn_cast<CmpInst>(inst);
						if(!cmpInst)
							DEBUG(errs() << "ERROR!! should be able to cast\n");

						DEBUG(errs() << *inst->getOperand(0) << ",," << *inst->getOperand(1) << "\n");
						if(!(binOp.a = getValidVar(binOp.a)))
							continue;
						if(!(binOp.b = getValidVar(binOp.b)))
							continue;
						binOp.op = cmpInst->getPredicate();
						DEBUG(errs() << "new cmp inst added: " << binOp << "\n");
						cmpInsts[v] = binOp;
						//cmpInsts
					}
				}
			}
			assignStarts(l);
			processList();

			if(indexVars.size() == 0)
			{
				DEBUG_WITH_TYPE("main", errs() << "No index Variable found\n");
				return false;
			}
			std::map<Value *,IndexVariable>::iterator ivit = indexVars.begin();
			std::pair<Value *, IndexVariable> ivinfo = *ivit;
			Value *indvar = ivinfo.first;
			IndexVariable *iv = &ivinfo.second;
			indexVars.clear();
			blist.clear();
			int nIterations;
			bool calc = false;
			if(Constant *s = dyn_cast<Constant>(iv->start))
				if(Constant *e = dyn_cast<Constant>(iv->end))
					if(Constant *inc = dyn_cast<Constant>(iv->inc)) 
					{
						nIterations = ((e->getUniqueInteger().operator-(s->getUniqueInteger())).sdiv(inc->getUniqueInteger())).getLimitedValue();
						calc = true;
					}
			if(!calc)
			{
				DEBUG_WITH_TYPE("main", errs() << "no of iterations not calculated\n");
				return false;
			}
			else
			{
				DEBUG_WITH_TYPE("main", errs() << "no of iterations: " << nIterations << "\n");
			}
			int ws[16] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
			std::vector<int> possible(ws,ws+16);
			for(std::vector<Instruction*>::iterator it = storeInsts.begin(); it != storeInsts.end(); it++)
			{
				Instruction *inst = *it;
				DEBUG_WITH_TYPE("main", errs() << "array assignment: " << *inst << "\n");
				Value *op0 = inst->getOperand(0);
				Value *op1 = inst->getOperand(1);
				std::vector<arrIndex*> rhs,lhs;
				DEBUG_WITH_TYPE("main", errs() << "parsing right: Size: " << rhs.size() << "\n\n");
				parseValue(op0,&rhs);
				DEBUG_WITH_TYPE("main", errs() << "After parsing right: Size: " << rhs.size() << "\n\n");
				parseValue(op1,&lhs);
				DEBUG_WITH_TYPE("main", errs() << "After parsing left: Size: " << lhs.size() << "\n");
				if(lhs.size() > 1)
				{
					DEBUG_WITH_TYPE("main", errs() << "There can only be 1 elem in lhs.. Something went wrong in parsing probably.. \n");
				}

				if(lhs.size() == 0)
					continue;
				//DEBUG_WITH_TYPE("main", errs() << *rhs[0]->first << ", " << *rhs[0]->second << "\n");
				if(rhs.size() > 0)
					filterArray(rhs,*lhs[0]);
				//DEBUG_WITH_TYPE("main", errs() << *rhs[0]->first << ", " << *rhs[0]->second << "\n");
				DEBUG_WITH_TYPE("main", errs() << "filtered rhs\n");
				int maxIter = getMaxIterations(rhs);
				DEBUG_WITH_TYPE("main", errs() << "Max Iterations: " << maxIter << "\n");
				std::map<std::string,bool> visited;
				int start = (dyn_cast<ConstantInt>(iv->start))->getZExtValue();
				int inc = (dyn_cast<ConstantInt>(iv->inc))->getZExtValue();
				int count = std::min(maxIter,nIterations);
				int end = start + inc*(count-1);
				for(int iter = start; iter <= end; iter += inc)
				{
					DEBUG_WITH_TYPE("main", errs() << "iter = " << iter << "\n");
					DEBUG_WITH_TYPE("main", errs() << "lhs: " << *((Value *) lhs[0]->first) << ", " << *((Value *) lhs[0]->second) << "\n");
					DEBUG_WITH_TYPE("main", errs() << "indvar: " << *indvar << "\n"); 
					arrelem *lhselem = getElemBySubs(lhs[0],iter,indvar);
					if(lhselem == NULL)
						break;
					std::string lhs_str = elemToString(lhselem);
					Node *n = new Node; 
					n->e = *lhselem;
					DEBUG_WITH_TYPE("main", errs() << "entering loop\n");
					for(std::vector<arrIndex*>::iterator elem = rhs.begin(); elem != rhs.end(); elem++)
					{
						if(*elem == NULL)
						{
							DEBUG_WITH_TYPE("main", errs() << "NULL elems\n");
						}
						arrIndex *ai = *elem;
						Value *v1 = (Value *) ai->first;
						Value *v2 = (Value *) ai->second;
						DEBUG_WITH_TYPE("main", errs() << "sizes: " << sizeof(*v1) << ", " << sizeof(*v2) << ", " << sizeof(Value) << "\n");
						DEBUG_WITH_TYPE("main", errs() << v1 << "\n"); 
						DEBUG_WITH_TYPE("main", errs() << v2 << "\n"); 
						DEBUG_WITH_TYPE("main", errs() << "rhs elem: " << ai << "\n");
						DEBUG_WITH_TYPE("main", errs() << "rhs elem: " << ((Value *) ai->first) << ", " << *((Value *) ai->second) << "\n");
						arrelem *e = getElemBySubs(ai,iter,indvar);
						if(e == NULL)
							break;
						std::string key = elemToString(e);
						DEBUG_WITH_TYPE("main", errs() << "key: " << key << "\n");
						Node *node;// = depTree[key];
						if(depTree.count(key) > 0)
						{
							DEBUG_WITH_TYPE("main", errs() << "key already exists\n");
							node = depTree[key];
							depTree[key]->parents.push_back(n);
							n->children.push_back(node);
							DEBUG_WITH_TYPE("main", errs() << "for key: " << key << " node: " << node << "\n");
						}
						else
						{
							DEBUG_WITH_TYPE("main", errs() << "key doesn't exist\n");
							Node *x = new Node;//(Node *) malloc(sizeof(Node));
							x->parents.push_back(n);
							DEBUG_WITH_TYPE("main", errs() << "key doesn't exist\n");
							x->e = *e;
							DEBUG_WITH_TYPE("main", errs() << "key doesn't exist\n");
							n->children.push_back(x);
							DEBUG_WITH_TYPE("main", errs() << "key doesn't exist\n");
							depTree[key] = x;
							DEBUG_WITH_TYPE("main", errs() << "key doesn't exist\n");
							visited[key] = false;
							DEBUG_WITH_TYPE("main", errs() << "for key: " << key << " node: " << depTree[key] << "\n");
						}
					}
					depTree[lhs_str] = n;
					visited[lhs_str] = false;
				}
				
				int maxw = 16;
				if(maxIter > 0)	
					maxw = doSearch(visited,depTree);
				DEBUG_WITH_TYPE("main", errs() << "maxw: " << maxw << "\n");
				for(int i = 0; i < possible.size(); i++)
				{
					if(possible[i] > maxw)
					{
						possible.erase(possible.begin()+i);
						i--;
					}
				}
				DEBUG_WITH_TYPE("main", errs() << "for inst: " << *inst << "\n SIMD Width: " << maxw << "\n");
				depTree.clear();
				visited.clear();
				/*
				for(std::vector<int>::iterator it = possible.begin(); it != possible.end(); it++) 
				{
					if(*it > maxw)
						possible.erase(it);
				}
				*/

			}
			errs() << "Required SIMD Width for the loop: " << possible[possible.size()-1] << "\n";
			return false;
		}

		int doSearch(std::map<std::string,bool> visited, std::map<std::string,Node*> tree)
		{
			int ans = 0;
			for(std::map<std::string,Node*>::iterator it = tree.begin(); it != tree.end(); it++)
			{
				if(visited[it->first])
					continue;
				DEBUG_WITH_TYPE("search", errs() << "new tree root: " << it->first << "\n");
				std::vector<Node*> stack;
				stack.push_back(it->second);
				while(stack.size() > 0)
				{
					Node *n = stack[stack.size()-1];
					if(n == NULL)
						DEBUG_WITH_TYPE("search", errs() << "stack node: NULL\n");
					std::string key = elemToString(&(n->e));
					DEBUG_WITH_TYPE("search", errs() << "stack node: " << key << "\n");
					stack.pop_back();
					if(visited[key])
						continue;
					visited[key] = true;
					if(n->parents.size() == 0)
						ans++;
					for(std::vector<Node*>::iterator child = n->children.begin(); child != n->children.end(); child++)
					{
						stack.push_back(*child);
					}
					for(std::vector<Node*>::iterator parent = n->parents.begin(); parent != n->parents.end(); parent++)
					{
						stack.push_back(*parent);
					}
				}
			}
			return ans;
		}

		void assignStarts(Loop *l)
		{
			for(std::map<Value *, IndexVariable>::iterator it = indexVars.begin(); it != indexVars.end(); it++)
			{
				Value *indVal = it->first;
				if(indexVars[indVal].start > 0)
					continue;
				for(Value::use_iterator ui = indVal->use_begin(); ui != indVal->use_end(); ui++)
				{
					if(Instruction *inst = dyn_cast<Instruction>(*ui))
					{
						if(inst->getOpcode() == Instruction::Store)
						{
							Value *other = (indVal == inst->getOperand(0) ? inst->getOperand(1) : inst->getOperand(0));
							DEBUG(errs() << "In assignStarts: other value: " << *other << "\n");
							if(!dyn_cast<Instruction>(other))
							{
								IndexVariable iv = it->second;
								DEBUG(errs() << "In assignStarts: IndexVariable retrieved: " << iv << "\n");
								iv.start = other;
								iv.level = l->getLoopDepth();
								updateIndexVar(indVal,iv);
							}
							//else
								//DEBUG(errs() << "shouldn't reach here as initialization is done with a constant\n");
						}
					}
				}
				
				BasicBlock *pre = l->getLoopPreheader();
				BasicBlock *header = l->getHeader();
				for(BasicBlock::iterator inst = pre->begin(); inst != pre->end(); inst++)
				{
					if(inst->getOpcode() == Instruction::Store && inst->getOperand(1) == indVal)
					{
						IndexVariable iv = indexVars[indVal];
						iv.start = inst->getOperand(0);
						iv.level = l->getLoopDepth();
						updateIndexVar(indVal, iv);
						//indexVars[indVal] = iv;
						//break;
					}
				}
				for(BasicBlock::iterator inst = header->begin(); inst != header->end(); inst++)
				{
					if(inst->getOpcode() == Instruction::Store && inst->getOperand(1) == indVal)
					{
						IndexVariable iv = indexVars[indVal];
						iv.start = inst->getOperand(0);
						iv.level = l->getLoopDepth();
						updateIndexVar(indVal, iv);
						//indexVars[indVal] = iv;
						//break;
					}
				}

			}
		}

		Value *assignEnds(Value *indVar, triplet cmpOp, IndexVariable iv)
		{
			DEBUG(errs() << "Assigning ends for: " << *indVar << "\n");
			Value *other = (indVar == cmpOp.a ? cmpOp.b : cmpOp.a);

			DEBUG(errs() << "Other value: " << *other << "\n");
			if(!dyn_cast<Instruction>(other))
			{
				//a constant
				int consValue,indStart,rhs,inc;
				if(ConstantInt *ci = dyn_cast<ConstantInt>(other))
					consValue = ci->getZExtValue();
				else
					return NULL;
				if(ConstantInt *ci = dyn_cast<ConstantInt>(iv.start))
					indStart = ci->getZExtValue();
				else
					return NULL;
				rhs = consValue - indStart;
				if(ConstantInt *ci = dyn_cast<ConstantInt>(iv.inc))
					inc = ci->getZExtValue() * iv.sign;
				else
					return NULL;
				DEBUG(errs() << "found all params, rhs: " << rhs << " inc: " << inc << "\n");
				switch(cmpOp.op)
				{
					case 34:
					case 35:
					case 39:
					case 38:
						//gt 
						if(inc == 0)
							return NULL;
						else if(inc > 0 && rhs > 0)
							return iv.start;
						else if(inc > 0)
							return NULL;
						else if(rhs >= 0)
							return iv.start;
						else
							return other;
					case 36:
					case 37:
					case 40:
					case 41:
						if(inc == 0)
							return NULL;
						else if(inc < 0 && rhs > 0)
							return iv.start;
						else if(inc < 0)
							return NULL;
						else if(inc > 0 && rhs <= 0)
							return iv.start;
						else
							return other;

				}
			}
			return NULL;
		}

		Value *getValidVar(Value *v)
		{
			DEBUG(errs() << "getting valid var for: " << v << "\n");
			if(!(v->hasName()))
			{
				DEBUG(errs() << "No name\n");
				if(loaded[v])
				{
					DEBUG(errs() << "loaded: " << loaded[v] << "\n");
					return loaded[v];
				}
				else
				{
					if(ConstantInt *ci = dyn_cast<ConstantInt>(v))
						return ci;
					return NULL;
				}
			}
			return v;
		}

		void processCmpVar(Value *v)
		{
			CmpInst *cmpInst = dyn_cast<CmpInst>(v);
			if(!cmpInst)
				DEBUG(errs() << "ERROR!! should be a cmp instruction\n");
			triplet cmpOp = cmpInsts[v];
			DEBUG(errs() << "Triplet : " << cmpOp << "\n");
			IndexVariable indVar;
			if(indexVars.count(cmpOp.a) > 0)
			{
				indVar = indexVars[cmpOp.a];
				indVar.end = assignEnds(cmpOp.a, cmpOp, indexVars[cmpOp.a]);
				updateIndexVar(cmpOp.a, indVar);
				//indexVars[cmpOp.a] = indVar;
			}
			else if(indexVars.count(cmpOp.b) > 0)
			{
				indVar = indexVars[cmpOp.b];
				indVar.end = assignEnds(cmpOp.b, cmpOp, indexVars[cmpOp.b]);
				updateIndexVar(cmpOp.b, indVar);
				indexVars[cmpOp.b] = indVar;
			}

		}

		void processList()
		{
			for(std::vector<Value *> :: iterator it = branchList.begin(); it != branchList.end(); it++)
			{
				DEBUG(errs() << "a branch instruction found.. cmp var: " << **it << "\n");
				processCmpVar(*it);
			}
		}

		void updateIndexVar(Value *v, IndexVariable iv) 
		{
			IndexVariable ivOld = indexVars[v];
			DEBUG(errs() << "Old index variable: " << ivOld << "\n");	
			DEBUG(errs() << "To be updated with: " << iv << "\n");	
			if(!iv.start)
				iv.start = ivOld.start;
			if(!iv.end)
				iv.end = ivOld.end;
			if(!iv.inc)
				iv.inc = ivOld.inc;
			if(iv.sign == 0)
				iv.sign = ivOld.sign;
			if(iv.level == -1)
				iv.level = ivOld.level;
			else if(iv.level > 0 && ivOld.level > iv.level)
				iv.level = ivOld.level;
				
			DEBUG(errs() << "new index variable: " << iv << "\n");
			indexVars[v] = iv;
			DEBUG(errs() << "After updating IndexVariable: " << indexVars[v] << "\n");
		}

		Value *getIncrement(Instruction *inst, Value *var)
		{
			Value *v = inst;
			Instruction *binOpInst = dyn_cast<Instruction>(v);
			if(binOpInst->getNumOperands() != 2)
				return NULL;
			Value *v1 = binOpInst->getOperand(0);
			Value *v2 = binOpInst->getOperand(1);
			Value *vL1 = loaded[v1];
			Value *vL2 = loaded[v2];
			if(v1->hasName() && v1->getValueName() == var->getValueName())
				return v2;
			else if(vL1 && vL1->hasName() && vL1->getValueName() == var->getValueName())
				return v2;
			else if(v2->hasName() && v2->getValueName() == var->getValueName())
				return v1;
			else if(vL2 && vL2->hasName() && vL2->getValueName() == var->getValueName())
				return v1;
			return NULL;
		}

		//only works for binary op instruction
		Value *constantValueInUse(Value *v)
		{
			Instruction *inst = dyn_cast<Instruction>(v);
			if(!inst)
			{
				DEBUG(errs() << "Error!! should be an instruction\n");
				return NULL;
			}
			if(inst->getNumOperands() != 2)
				return NULL;
			Value *v1 = inst->getOperand(0);
			Value *v2 = inst->getOperand(1);
			if(!dyn_cast<Instruction>(v1))
				return v1;
			else if(!dyn_cast<Instruction>(v2))
				return v2;
			return NULL;
		}

		//only works for binary op instructions
		Value *similarValueInUse(Value *v)
		{
			Instruction *inst = dyn_cast<Instruction>(v);
			if(!inst)
			{
				DEBUG(errs() << "Error!! should be an instruction\n");
				return NULL;
			}
			if(inst->getNumOperands() != 2)
				return NULL;
			if(!v->hasName())
				return NULL;
			ValueName *vn = v->getValueName();
			DEBUG(errs() << "value name: " << v->getName() << "\n");
			//Value *v1 = v->getOperand(0);
			//Value *v2 = v->getOperand(1);
			int index = 0;
			for(User::op_iterator ui = inst->op_begin(); ui != inst->op_end(); index++,ui++)
			{
				DEBUG(errs() << "User: " << **ui << "\n");
				Value *uiVal = dyn_cast<Value>(*ui);
				if(!uiVal)
				{
					DEBUG(errs() << "ERROR!! should never occur as all operands(uses) are values\n");
					continue;
				}
				if(uiVal->hasName() && vn == uiVal->getValueName())
					return uiVal;
				//goes only 1 level up.. But that is the case most of the times..
				if(LoadInst *li = dyn_cast<LoadInst>(uiVal))
				{
					Value *v1 = li->getOperand(0);
					DEBUG(errs() << "v1: " << *v1 << "\n");
					DEBUG(errs() << "v1 name: " << v1->getName() << " " << "\n");
					if(v1->hasName() && v1->getValueName() == vn)
						return uiVal;
				}
			}
			return NULL;
		}

		void filterArray(std::vector<arrIndex*>& arr, arrIndex ref)
		{
			DEBUG_WITH_TYPE("filter", errs() << "filtering wrt: " << *ref.first << "\n");
			/*
			for(std::vector<arrIndex>::iterator it = arr.begin(); it != arr.end(); it++)
			{
				DEBUG_WITH_TYPE("filter", errs() << "elem: " << *it->first << ", " << *it->second << "\n");
				if(it->first != ref.first)
				{
					DEBUG_WITH_TYPE("filter", errs() << "erasing this elem\n");
					arr.erase(it);
				}
			}
			*/
			for(int i = 0; i < arr.size(); i++)
			{
				std::vector<arrIndex*>::iterator it = arr.begin()+i;
				DEBUG_WITH_TYPE("filter", errs() << "elem: " << *(*it)->first << ", " << *(*it)->second << "\n");
				DEBUG_WITH_TYPE("filter", errs() << "size: " << arr.size() << "\n");
				if((*it)->first != ref.first)
				{
					arr.erase(it);
					i--;
					DEBUG_WITH_TYPE("filter", errs() << "erasing this elem\n");
					DEBUG_WITH_TYPE("filter", errs() << "after erasing size: " << arr.size() << "\n");
				}
			}
		}

		int getMaxIterations(std::vector<arrIndex*> arr)
		{
			int ans = 0;
			for(int i = 0; i < arr.size(); i++)
			{
				if(Instruction *inst = dyn_cast<Instruction>(arr[i]->second))
				{
					DEBUG_WITH_TYPE("maxIterations", errs() << "op Instruction: " << *inst << "\n");
					if(inst->getOpcode() == Instruction::Add || inst->getOpcode() == Instruction::Sub)
					{
						Value *op0 = inst->getOperand(0);
						Value *op1 = inst->getOperand(1);
						if(ConstantInt *ci = dyn_cast<ConstantInt>(op0))
						{
							int c = ci->getUniqueInteger().getLimitedValue();
							DEBUG_WITH_TYPE("maxIterations", errs() << "Constant in op: " << c << "\n");
							ans = max(ans, c);
						}
						else if(ConstantInt *ci = dyn_cast<ConstantInt>(op1))
						{
							int c = ci->getUniqueInteger().getLimitedValue();
							DEBUG_WITH_TYPE("maxIterations", errs() << "Constant in op: " << c << "\n");
							ans = max(ans, c); 
						}
						else
						{
							DEBUG_WITH_TYPE("maxIterations", errs() << "No constant in inst\n");
							return 0;
						}
					}
					else if(inst->getOpcode() == Instruction::Load || inst->getOpcode() == Instruction::Store)
					{
						continue;
					}
					else
						return 0;
				}
				else
				{
					return 0;
				}
			}
			DEBUG_WITH_TYPE("maxIterations", errs() << "Max Iterations = " << ans << "\n");
			return ans;
		}

		IndexVariable *getIV(Loop *l,Value *indvar)
		{
			Value *v = l->getCanonicalInductionVariable();
			DEBUG_WITH_TYPE("iv", errs() << "iv: " << *v << "\n");
			IndexVariable *iv = (IndexVariable *) malloc(sizeof(IndexVariable));
			return iv;
		}

		void parseValue(Value *v, std::vector<arrIndex*> *l)
		{
			DEBUG_WITH_TYPE("main", errs() << "address of vector space: " << l << "\n");
			if(v == NULL)
			{
				DEBUG_WITH_TYPE("parse", errs() << "exiting from parse\n");
				return;
			}
			DEBUG_WITH_TYPE("parse", errs() << "Parse Value: " << *v << "\n");
			Instruction *inst = dyn_cast<Instruction>(v);
			if(inst == NULL)
			{
				DEBUG_WITH_TYPE("parse", errs() << "exiting from parse\n");
				return;
			}
			arrIndex *ai = (arrIndex *) malloc(sizeof(arrIndex));
			if(inst->getOpcode() == Instruction::Add || inst->getOpcode() == Instruction::Sub)
			{
				Instruction *op0 = dyn_cast<Instruction>(inst->getOperand(0));
				Instruction *op1 = dyn_cast<Instruction>(inst->getOperand(1));
				if(op0 != NULL)
					parseValue(getValidVar(op0), l);
				if(op1 != NULL)
					parseValue(getValidVar(op1), l);
			}
			else if(inst->getOpcode() == Instruction::GetElementPtr)
			{
				DEBUG_WITH_TYPE("parse", errs() << "Gep Instruction: " << *inst << "\n");
				DEBUG_WITH_TYPE("parse", errs() << "No of operands: " << inst->getNumOperands() << "\n"); 
				Value *addr = inst->getOperand(2);
				Instruction *addrInst = dyn_cast<Instruction>(addr);
				Instruction *allocInst = dyn_cast<Instruction>(inst->getOperand(0));
				DEBUG_WITH_TYPE("parse", errs() << "Address: " << *addr << "\n");
				if(allocInst && allocInst->getOpcode() == Instruction::Alloca)
				{
					DEBUG_WITH_TYPE("parse", errs() << "rhs addr: " << allocInst << "\n");
					ai->first = allocInst;
					DEBUG_WITH_TYPE("parse", errs() << "lhs addr: " << ai->first << "\n");
					if(addrInst)
					{
						if(addrInst->getOpcode() >= 33 && addrInst->getOpcode() <= 44)
						{
							addrInst = dyn_cast<Instruction>(addrInst->getOperand(0));
							DEBUG_WITH_TYPE("parse", errs() << "Addr instruction: " << *addrInst << "\n");
						}
						ai->second = addrInst;
					}
					else
					{
						ai->second = addr;
					}
					DEBUG_WITH_TYPE("parse", errs() << "new arrindex: " << *(ai->first) << "," << *(ai->second) << "\n");
					DEBUG_WITH_TYPE("parse", errs() << "Before pushing size: " << l->size() << "\n");
					l->push_back(ai);
					DEBUG_WITH_TYPE("parse", errs() << "After pushing size: " << l->size() << "\n");
					DEBUG_WITH_TYPE("parse", errs() << "After pushing arrIndex: " << *((*l)[l->size()-1]->first) << *((*l)[l->size()-1]->second) << "\n");
				}
				else
					DEBUG_WITH_TYPE("parse", errs() << "Undefined Behaviour\n");
			}
			else if(inst->getOpcode() == Instruction::Load)
			{
				parseValue(inst->getOperand(0), l);
			}
			else
			{
				DEBUG_WITH_TYPE("parse", errs() << "exiting from parse\n");
				return;
			}
			DEBUG_WITH_TYPE("parse", errs() << "exiting from parse\n");
		}

		bool getValueBySubs(Value *v, int n, int *ret, Value *iv)
		{
			if(v == NULL)
				return false;
			Instruction *inst = dyn_cast<Instruction>(v);
			if(inst != NULL)
			{
				if(inst->getOpcode() == Instruction::Alloca)
				{
					if(inst == iv)
					{
						*ret = n;
						return true;
					}
					else
						return false;
				}
				else if(inst->getOpcode() == Instruction::Load)
				{
					inst = dyn_cast<Instruction>(inst->getOperand(0));
					if(!inst || inst != iv)
						return false;
					*ret = n;
					return true;
				}
				else if(inst->getOpcode() == Instruction::Add)
				{
					int val1,val2;
					if(getValueBySubs(inst->getOperand(0),n,&val1,iv))
					{
						if(getValueBySubs(inst->getOperand(1),n,&val2,iv))
						{
							*ret = val1 + val2;
							return true;
						}
						else
							return false;
					}
					else
						return false;
				}
				else if(inst->getOpcode() == Instruction::Sub)
				{
					int val1,val2;
					if(getValueBySubs(inst->getOperand(0),n,&val1,iv))
					{
						if(getValueBySubs(inst->getOperand(1),n,&val2,iv))
						{
							*ret = val1 - val2;
							return true;
						}
						else
							return false;
					}
					else
						return false;
				}
				else
				{
					return false;
				}
			}
			else if(ConstantInt *ci = dyn_cast<ConstantInt>(v))
			{
				*ret = ci->getUniqueInteger().getLimitedValue();
				return true;
			}
			else
				return false;
		}

		arrelem *getElemBySubs(arrIndex *ai, int iter, Value *iv)
		{
			DEBUG_WITH_TYPE("subs", errs() << "substituting in: " << *(ai->first) << ", " << *(ai->second) << " for iter = " << iter << "\n");
			DEBUG_WITH_TYPE("subs", errs() << "input value: " << iv << "\n");
			arrelem *elem = (arrelem *) malloc(sizeof(arrelem));
			DEBUG_WITH_TYPE("subs", errs() << "array: " << ai->first->getName() << "\n");
			std::string arrname = ((ai->first)->getName()).str();
			DEBUG_WITH_TYPE("subs", errs() << "size of string: " << sizeof(arrname) << " size of elem: " << sizeof(arrelem) << "\n");
			//elem->first.copy((char *) arrname.data(), arrname.length(), 0);
			elem->first = (char *) malloc(strlen(arrname.data()));
			strcpy(elem->first, arrname.data());
			//DEBUG_WITH_TYPE("subs", errs() << "array name: " << elem->first << "\n");
			Instruction *inst = dyn_cast<Instruction>(ai->second);
			if(inst)
			{
				//DEBUG_WITH_TYPE("subs", errs() << "subs instruction: " << *inst << "\n\n\n");
				if(inst->getOpcode() == Instruction::Alloca || inst->getOpcode() == Instruction::Load)
				{
					DEBUG_WITH_TYPE("subs", errs() << "Load/Alloc Instruction\n");
					Value *v = getValidVar((Value *) inst);
					if(v == iv)
						elem->second = iter;
					else
						elem->second = 0;
				}
				else if(inst->getOpcode() == Instruction::Add || inst->getOpcode() == Instruction::Sub)
				{
					Value *op0 = inst->getOperand(0);
					Value *op1 = inst->getOperand(1);
					if(ConstantInt *ci = dyn_cast<ConstantInt>(op0))
					{
						int val;
						if(!getValueBySubs(op1,iter,&val,iv))
							return NULL;
						if(inst->getOpcode() == Instruction::Add)
							elem->second = val + ci->getUniqueInteger().getLimitedValue();
						else
							elem->second = val - ci->getUniqueInteger().getLimitedValue();
					}
					else if(ConstantInt *ci = dyn_cast<ConstantInt>(op1))
					{
						int val;
						if(!getValueBySubs(op0,iter,&val,iv))
							return NULL;
						if(inst->getOpcode() == Instruction::Add)
							elem->second = val + ci->getUniqueInteger().getLimitedValue();
						else
							elem->second = val - ci->getUniqueInteger().getLimitedValue();
					}
					else
					{
						return NULL;
					}
				}
				else
				{
					return NULL;
				}
			}
			else
			{
				ConstantInt *ci = dyn_cast<ConstantInt>(ai->second);
				if(!ci)
					DEBUG_WITH_TYPE("subs", errs() << "Unexpected behaviour\n");
				elem->second = ci->getUniqueInteger().getLimitedValue();
			}
			DEBUG_WITH_TYPE("subs", errs() << "substituted elem: " << elem->first << ", " << elem->second << "\n");
			if(elem == NULL)
				return NULL;
			DEBUG_WITH_TYPE("subs", errs() << "returning elem: " << elem->first << "," << elem->second << "\n");
			return elem;
		}

		char *elemToString(arrelem *elem)
		{
			DEBUG_WITH_TYPE("elemtostr", errs() << "elem: " << elem->first << ", " << elem->second << "\n");
			char *name = elem->first;
			int len = strlen(name);
			DEBUG_WITH_TYPE("elemtostr", errs() << "length of name: " << len << "\n");
			char s[32];
			sprintf(s,"%d",elem->second);
			DEBUG_WITH_TYPE("elemtostr", errs() << "index value: " << s << "\n");
			char *ret = (char *) malloc(len+33);
			strcpy(ret,name);
			strcat(ret,"_");
			strcat(ret,s);
			DEBUG_WITH_TYPE("elemtostr", errs() << "returning from elemtostr: " << ret << "\n");
			return ret;
			//return std::string(elem->first) + std::string(s);
		}

	};

}

char ProjectPass :: ID = 0;
static RegisterPass<ProjectPass> X("projectTest", "Project Pass", false, false);
