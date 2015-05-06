package org.scribble2.model;

import org.scribble2.model.name.SimpleKindedNameNode;
import org.scribble2.model.visit.ModelVisitor;
import org.scribble2.sesstype.kind.RecursionVarKind;
import org.scribble2.util.ScribbleException;

public abstract class Recursion<T extends ProtocolBlock<? extends InteractionSequence<? extends InteractionNode>>>
		extends CompoundInteractionNode
{
	//public final RecursionVarNode recvar;
	public final SimpleKindedNameNode<RecursionVarKind> recvar;
	public final T block;

	/*protected Recursion(CommonTree ct, RecursionVarNode recvar, T block)
	{
		this(ct, recvar, block, null, null);
	}

	protected Recursion(CommonTree ct, RecursionVarNode recvar, T block, CompoundInteractionNodeContext cicontext)
	{
		this(ct, recvar, block, cicontext, null);
	}*/

	//protected Recursion(RecursionVarNode recvar, T block)//, CompoundInteractionNodeContext cicontext, Env env)
	protected Recursion(SimpleKindedNameNode<RecursionVarKind> recvar, T block)//, CompoundInteractionNodeContext cicontext, Env env)
	{
		this.recvar = recvar;
		this.block = block;
	}

	//protected abstract Recursion<T> reconstruct(RecursionVarNode recvar, T block);
	protected abstract Recursion<T> reconstruct(SimpleKindedNameNode<RecursionVarKind> recvar, T block);

	@Override
	public Recursion<T> visitChildren(ModelVisitor nv) throws ScribbleException
	{
		//RecursionVarNode recvar = (RecursionVarNode) visitChild(this.recvar, nv);
		SimpleKindedNameNode<RecursionVarKind> recvar = SimpleKindedNameNode.castSimpleKindedNameNode(RecursionVarKind.KIND, visitChild(this.recvar, nv));
		T block = visitChildWithClassCheck(this, this.block, nv);
		//return new Recursion<>(this.ct, recvar, block, getContext(), getEnv());
		return reconstruct(recvar, block);//, getContext(), getEnv());
	}

	/*@Override
	public NodeContextBuilder enterContextBuilding(NodeContextBuilder builder) throws ScribbleException
	{
		builder.pushContext(new CompoundInteractionNodeContext());
		return builder;
	}

	@Override
	public Recursion<T> leaveContextBuilding(NodeContextBuilder builder) throws ScribbleException
	{
		CompoundInteractionNodeContext rcontext = (CompoundInteractionNodeContext) builder.popContext();
		rcontext = (CompoundInteractionNodeContext) rcontext.merge(this.block.getContext());
		builder.replaceContext(((CompoundInteractionContext) builder.peekContext()).merge(rcontext));
		//return new Recursion<>(this.ct, this.recvar, this.block, rcontext);
		return reconstruct(this.ct, this.recvar, this.block, rcontext, getEnv());
	}

	@Override
	public Recursion<T> leaveWFChoiceCheck(WellFormedChoiceChecker checker) throws ScribbleException
	{
		checker.getEnv().leave(this, checker);
		return this;
	}

	@Override
	public ReachabilityChecker enterReachabilityCheck(ReachabilityChecker checker) throws ScribbleException
	{
		checker.getEnv().enter(this, checker);
		return checker;
	}

	@Override
	public Recursion<T> leaveReachabilityCheck(ReachabilityChecker checker) throws ScribbleException
	{
		checker.getEnv().leave(this, checker);
		return this;
	}*/
	
	/*@Override
	public Env enter(EnvVisitor nv) throws ScribbleException
	{
		Env env = new Env(super.enter(nv));
		RecursionLabel lab = this.lab.toName();
		env.labs.add(lab);

		
		env.roles.enterNonEnablingContext();
		

		return env;
	}
	
	@Override
	public Recursion leave(EnvVisitor nv) throws ScribbleException
	{
		Recursion gr = (Recursion) super.leave(nv);
		Env env = new Env(nv.getEnv());
		env.labs.remove(this.lab.toName());
		nv.setEnv(env);
		return gr;
	}*/
	
	@Override
	public String toString()
	{
		return Constants.REC_KW + " " + this.recvar + " " + block;
	}
}
