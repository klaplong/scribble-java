package org.scribble.del.local;

import org.scribble.ast.AstFactoryImpl;
import org.scribble.ast.ScribNode;
import org.scribble.ast.local.LProtocolBlock;
import org.scribble.ast.local.LRecursion;
import org.scribble.ast.name.simple.RecVarNode;
import org.scribble.del.RecursionDel;
import org.scribble.main.ScribbleException;
import org.scribble.sesstype.name.RecVar;
import org.scribble.visit.EndpointGraphBuilder;
import org.scribble.visit.ProjectedChoiceSubjectFixer;
import org.scribble.visit.ProtocolDefInliner;
import org.scribble.visit.ReachabilityChecker;
import org.scribble.visit.env.InlineProtocolEnv;
import org.scribble.visit.env.ReachabilityEnv;

public class LRecursionDel extends RecursionDel implements LCompoundInteractionNodeDel
{
	@Override
	public ScribNode leaveProtocolInlining(ScribNode parent, ScribNode child, ProtocolDefInliner inl, ScribNode visited) throws ScribbleException
	{
		LRecursion gr = (LRecursion) visited;
		RecVarNode recvar = gr.recvar.clone();
		LProtocolBlock block = (LProtocolBlock) ((InlineProtocolEnv) gr.block.del().env()).getTranslation();	
		LRecursion inlined = AstFactoryImpl.FACTORY.LRecursion(recvar, block);
		inl.pushEnv(inl.popEnv().setTranslation(inlined));
		return (LRecursion) super.leaveProtocolInlining(parent, child, inl, gr);
	}

	@Override
	public LRecursion leaveReachabilityCheck(ScribNode parent, ScribNode child, ReachabilityChecker checker, ScribNode visited) throws ScribbleException
	{
		LRecursion lr = (LRecursion) visited;
		ReachabilityEnv env = checker.popEnv().mergeContext((ReachabilityEnv) lr.block.del().env());
		env = env.removeContinueLabel(lr.recvar.toName());
		checker.pushEnv(env);
		return (LRecursion) LCompoundInteractionNodeDel.super.leaveReachabilityCheck(parent, child, checker, visited);  // records the current checker Env to the current del; also pops and merges that env into the parent env*/
	}
	
	@Override
	public void enterEndpointGraphBuilding(ScribNode parent, ScribNode child, EndpointGraphBuilder graph)
	{
		super.enterEndpointGraphBuilding(parent, child, graph);
		LRecursion lr = (LRecursion) child;
		RecVar rv = lr.recvar.toName();
		// Update existing state, not replace it -- cf. LDoDel
		////conv.builder.addEntryLabel(rv);
		//graph.builder.pushRecursionEntry(rv, null);
		
		/*if (graph.builder.isUnguardedInChoice())  // Actually, not needed since unfoldings are enough to make graph building work (and this makes combined unguarded choice-rec and continue protocols work)
		{
			// Using "previous" entry for this rec lab works because unguarded recs already unfolded (including nested recvar shadowing -- if unguarded choice-rec, it will be unfolded and rec entry recorded for guarded unfolding)
			graph.builder.pushRecursionEntry(rv, graph.builder.getRecursionEntry(rv));
		}
		else*/
		{
			graph.builder.addEntryLabel(rv);
			graph.builder.pushRecursionEntry(rv, graph.builder.getEntry());
		}
	}

	@Override
	public LRecursion leaveEndpointGraphBuilding(ScribNode parent, ScribNode child, EndpointGraphBuilder graph, ScribNode visited)
	{
		LRecursion lr = (LRecursion) visited;
		RecVar rv = lr.recvar.toName();
		graph.builder.popRecursionEntry(rv);
		return (LRecursion) super.leaveEndpointGraphBuilding(parent, child, graph, lr);
	}

	@Override
	public void enterProjectedChoiceSubjectFixing(ScribNode parent, ScribNode child, ProjectedChoiceSubjectFixer fixer)
	{
		fixer.pushRec(((LRecursion) child).recvar.toName());
	}
	
	@Override
	public ScribNode leaveProjectedChoiceSubjectFixing(ScribNode parent, ScribNode child, ProjectedChoiceSubjectFixer fixer, ScribNode visited)
	{
		fixer.popRec(((LRecursion) child).recvar.toName());
		return visited;
	}
}
