/**
 * Copyright 2008 The Scribble Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */
package org.scribble.model.global;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import org.scribble.model.MPrettyPrint;
import org.scribble.model.global.actions.SAction;
import org.scribble.type.Payload;
import org.scribble.type.name.GProtocolName;
import org.scribble.type.name.Role;

public class SGraph implements MPrettyPrint
{
	public final GProtocolName proto;
	//private final Map<Role, EGraph> efsms;
	//private final boolean fair;

	public final SState init;
	public Map<Integer, SState> states; // State ID -> GMState

	private Map<Integer, Set<Integer>> reach; // State ID -> reachable states (not reflexive)
	private Set<Set<Integer>> termSets;

	// Unlike EState, SGraph is not just a "simple wrapper" for an existing graph of nodes -- it is a "semantic structure" that needs to be fully built properly (so no arbitrary "toGraph" method; cf., EState)
	protected SGraph(GProtocolName proto, Map<Integer, SState> states, SState init)
	{
		this.proto = proto;
		this.init = init;
		this.states = Collections.unmodifiableMap(states);
		this.reach = getReachabilityMap();
	}

	/*public SModel toModel()
	{
		return new SModel(this);
	}*/

	public Set<Set<Integer>> getTerminalSets()
	{
		if (this.termSets != null)
		{
			return this.termSets;
		}

		Set<Set<Integer>> termSets = new HashSet<>();
		Set<Set<Integer>> checked = new HashSet<>();
		for (Integer i : reach.keySet())
		{
			SState s = this.states.get(i);
			Set<Integer> rs = this.reach.get(s.id);
			if (!checked.contains(rs) && rs.contains(s.id))
			{
				checked.add(rs);
				if (isTerminalSetMember(s))
				{
					termSets.add(rs);
				}
			}
		}
		this.termSets = Collections.unmodifiableSet(termSets);
		return this.termSets;
	}

	private boolean isTerminalSetMember(SState s)
	{
		Set<Integer> rs = this.reach.get(s.id);
		Set<Integer> tmp = new HashSet<>(rs);
		tmp.remove(s.id);
		for (Integer r : tmp)
		{
			if (!this.reach.containsKey(r) || !this.reach.get(r).equals(rs))
			{
				return false;
			}
		}
		return true;
	}

	// Pre: reach.get(start).contains(end) // FIXME: will return null if initial
	// state is error
	public List<SAction> getTrace(SState start, SState end)
	{
		SortedMap<Integer, Set<Integer>> candidates = new TreeMap<>();
		Set<Integer> dis0 = new HashSet<Integer>();
		dis0.add(start.id);
		candidates.put(0, dis0);

		Set<Integer> seen = new HashSet<>();
		seen.add(start.id);

		return getTraceAux(new LinkedList<>(), seen, candidates, end);
	}

	// Djikstra's
	private List<SAction> getTraceAux(List<SAction> trace, Set<Integer> seen,
			SortedMap<Integer, Set<Integer>> candidates, SState end)
	{
		Integer dis = candidates.keySet().iterator().next();
		Set<Integer> cs = candidates.get(dis);
		Iterator<Integer> it = cs.iterator();
		Integer currid = it.next();
		it.remove();
		if (cs.isEmpty())
		{
			candidates.remove(dis);
		}

		SState curr = this.states.get(currid);
		Iterator<SAction> as = curr.getAllActions().iterator();
		Iterator<SState> ss = curr.getAllSuccessors().iterator();
		while (as.hasNext())
		{
			SAction a = as.next();
			SState s = ss.next();
			if (s.id == end.id)
			{
				trace.add(a);
				return trace;
			}

			if (!seen.contains(s.id) && this.reach.containsKey(s.id)
					&& this.reach.get(s.id).contains(end.id))
			{
				seen.add(s.id);
				Set<Integer> tmp1 = candidates.get(dis + 1);
				if (tmp1 == null)
				{
					tmp1 = new HashSet<>();
					candidates.put(dis + 1, tmp1);
				}
				tmp1.add(s.id);
				List<SAction> tmp2 = new LinkedList<>(trace);
				tmp2.add(a);
				List<SAction> res = getTraceAux(tmp2, seen, candidates, end);
				if (res != null)
				{
					return res;
				}
			}
		}
		return null;
	}

	// Not reflexive
	public Map<Integer, Set<Integer>> getReachabilityMap()
	{
		if (this.reach != null)
		{
			return this.reach;
		}

		Map<Integer, Integer> idToIndex = new HashMap<>(); // state ID -> array index
		Map<Integer, Integer> indexToId = new HashMap<>(); // array index -> state ID
		int i = 0;
		for (SState s : this.states.values())
		{
			idToIndex.put(s.id, i);
			indexToId.put(i, s.id);
			i++;
		}
		this.reach = getReachabilityAux(idToIndex, indexToId);

		return this.reach;
	}

	private Map<Integer, Set<Integer>> getReachabilityAux(
			Map<Integer, Integer> idToIndex, Map<Integer, Integer> indexToId)
	{
		int size = idToIndex.keySet().size();
		boolean[][] reach = new boolean[size][size];

		for (Integer s1id : idToIndex.keySet())
		{
			for (SState s2 : this.states.get(s1id).getAllSuccessors())
			{
				reach[idToIndex.get(s1id)][idToIndex.get(s2.id)] = true;
			}
		}

		for (boolean again = true; again;)
		{
			again = false;
			for (int i = 0; i < size; i++)
			{
				for (int j = 0; j < size; j++)
				{
					if (reach[i][j])
					{
						for (int k = 0; k < size; k++)
						{
							if (reach[j][k] && !reach[i][k])
							{
								reach[i][k] = true;
								again = true;
							}
						}
					}
				}
			}
		}

		Map<Integer, Set<Integer>> res = new HashMap<>();
		for (int i = 0; i < size; i++)
		{
			Set<Integer> tmp = res.get(indexToId.get(i));
			for (int j = 0; j < size; j++)
			{
				if (reach[i][j])
				{
					if (tmp == null)
					{
						tmp = new HashSet<>();
						res.put(indexToId.get(i), tmp);
					}
					tmp.add(indexToId.get(j));
				}
			}
		}

		return Collections.unmodifiableMap(res);
	}

	private String toCanonProtocol(List<CanonProtocolEntry> entries, int idx,
			Set<Integer> path, Set<Integer> vars)
	{
		CanonProtocolEntry entry = entries.get(idx);
		String out = entry.from.toString() + "->" + entry.to.toString() + ":{";

		for (int i = 0; i < entry.options.size(); i ++)
		{
			if (i > 0)
			{
				out += ", ";
			}

			CanonProtocolOption option = entry.options.get(i);
			out += i + "<" + option.type + ">.";

			if (option.next == -1)
			{
				out += "end";
			}
			else if (path.contains(option.next))
			{
				out += "X" + option.next;
				vars.add(option.next);
			}
			else
			{
				Set<Integer> newpath = new HashSet<>(path);
				newpath.add(idx);
				out += toCanonProtocol(entries, option.next, newpath, vars);
			}
		}

		out += "}";

		if (vars.contains(idx))
		{
			out = "mX" + idx + "." + out;
		}

		return out;
	}

	private Set<String> canonToRoleStrs(
			List<CanonProtocolEntry> entries, int idx,
			Set<Integer> visited) {
		Set<String> myRoleStrings = new HashSet<>();
		CanonProtocolEntry entry = entries.get(idx);

		myRoleStrings.add(entry.from.toString());
		myRoleStrings.add(entry.to.toString());

		for (int i = 0; i < entry.options.size(); i ++)
		{
			if (visited.contains(i))
			{
				continue;
			}
			visited.add(i);

			myRoleStrings.addAll(
				canonToRoleStrs(entries, entry.options.get(i).next, visited));
		}

		return myRoleStrings;
	}

	private int buildCanonProtocol(SState state,
			List<CanonProtocolEntry> entries,
			Map<SState, Integer> stateIdxs)
	{
		// Assumes the current state is not processed yet (not in stateIdxs).

		List<SAction> actions = state.getAllActions();

		CanonProtocolEntry entry = null;
		int idx = -1;

		// Add the current state as an entry if it has outgoing actions.
		// This needs to be done now, because otherwise we get an infinite loop
		// when a following state loops back here.
		for (int i = 0; i < actions.size(); i ++)
		{
			SAction action = actions.get(i);

			if (action.isSend())
			{
				entry = new CanonProtocolEntry(action.subj, action.obj);
				break;
			}
		}

		if (entry != null)
		{
			idx = entries.size();
			entries.add(entry);
			stateIdxs.put(state, idx);
		}

		// Follow outgoing edges.
		for (int i = 0; i < actions.size(); i ++)
		{
			SAction action = actions.get(i);

			SState next = state.getSuccessor(action);
			Integer nextIdx = stateIdxs.get(next);

			if (nextIdx == null)
			{
				nextIdx = buildCanonProtocol(next, entries, stateIdxs);
			}

			// Forward the next state's entry idx if this one has no entry.
			if (idx == -1)
			{
				idx = nextIdx;
			}

			// Add send actions as option. Note that now the entry is created,
			// since we have looked for the first send action before.
			if (action.isSend())
			{
				entry.options.add(
						new CanonProtocolOption(action.payload, nextIdx));
			}
		}

		return idx;
	}

	private Pair<Integer,Integer> buildCC0Templ(
			List<CanonProtocolEntry> entries,
			int idx, // current entry idx.
			String[] roles, // we only need the names of the roles.
			String argStr, // for recursive calls.
			Map<Integer,Integer> path, // which graph idxs were assigned
									   // what medium nr.
			Map<String, Map<Integer,Integer>> idxTypes, // role type nrs per idx.
			Map<String,Integer> nrsOfTypes, // nr of types per role.
			Map<String,Integer> nextTypes, // what type nr follows.
			Map<String,Map<Integer,LineOfCode>> typedefs, // per role & type.
			Map<String,Map<Integer,List<LineOfCode>>> choices, // per role & type.
			Map<Integer,List<LineOfCode>> mediums, // per type.
			Map<Integer,LineOfCode> mediumDecs, // medium declarations.
			int nrOfVars, int nrOfMediums)
	{
		CanonProtocolEntry entry = entries.get(idx);
		int mediumNr = nrOfMediums ++;

		int fromTypeNr = nrsOfTypes.get(entry.fromStr);
		int toTypeNr = nrsOfTypes.get(entry.toStr);

		idxTypes.get(entry.fromStr).put(idx, fromTypeNr);
		idxTypes.get(entry.toStr).put(idx, toTypeNr);

		LineOfCode typedefFrom = new LineOfCode(
				String.format("typedef <!choice c%s_%d> t%1$s_%2$d;",
					entry.fromStr, fromTypeNr), 0);
		typedefs.get(entry.fromStr).put(fromTypeNr, typedefFrom);

		List<LineOfCode> choiceFrom = new ArrayList<>();
		choices.get(entry.fromStr).put(fromTypeNr, choiceFrom);

		LineOfCode typedefTo = new LineOfCode(
				String.format("typedef <?choice c%s_%d> t%1$s_%2$d;",
					entry.toStr, toTypeNr), 0);
		typedefs.get(entry.toStr).put(toTypeNr, typedefTo);
		choiceFrom.add(new LineOfCode(
				String.format("choice c%s_%d {", entry.fromStr, fromTypeNr),
				0));

		List<LineOfCode> choiceTo = new ArrayList<>();
		choices.get(entry.toStr).put(toTypeNr, choiceTo);
		choiceTo.add(new LineOfCode(
				String.format("choice c%s_%d {", entry.toStr, toTypeNr), 0));

		List<LineOfCode> medium = new ArrayList<>();
		mediums.put(mediumNr, medium);

		// Because the types of non-senders/-recipients are the same across the
		// following branches, we can just use the results from the last branch
		// followed.
		Map<String,Integer> newNrsOfTypes = null;

		// Store the current nr of types (current type nr) of each role to
		// generate the parameter list later.
		Map<String,Integer> nrsOfTypesBeforeRec = new HashMap<>(nrsOfTypes);

		// Only update the nr of types of the sender and recipient after
		// generating the parameters.
		nrsOfTypes.put(entry.fromStr, fromTypeNr+1);
		nrsOfTypes.put(entry.toStr, toTypeNr+1);

		medium.add(new LineOfCode(
				String.format("switch ($%s) {", entry.fromStr), 1));

		for (int i = 0; i < entry.options.size(); i ++)
		{
			CanonProtocolOption opt = entry.options.get(i);

			medium.add(new LineOfCode(
					String.format("case l%s_%d_%d:",
						entry.fromStr, fromTypeNr, i), 1));
			// Receive value.
			medium.add(new LineOfCode(
					String.format("%s v%d = recv($%s);",
						opt.type, nrOfVars, entry.fromStr), 2));
			// Select at recipient.
			medium.add(new LineOfCode(
					String.format("$%s.l%1$s_%d_%d;",
						entry.toStr, toTypeNr, i), 2));
			// Send value.
			medium.add(new LineOfCode(
					String.format("send($%s, v%d);",
						entry.toStr, nrOfVars ++), 2));

			if (opt.next == -1)
			{
				for (int j = 0; j < roles.length; j ++)
				{
					medium.add(new LineOfCode(
							String.format("wait($%s);", roles[j]), 2));
				}

				choiceFrom.add(new LineOfCode(
						String.format("<!%s;> l%s_%d_%d;",
							opt.type, entry.fromStr, fromTypeNr, i), 1));
				choiceTo.add(new LineOfCode(
						String.format("<?%s;> l%s_%d_%d;",
							opt.type, entry.toStr, toTypeNr, i), 1));
			}

			else if (path.containsKey(opt.next))
			{
				medium.add(new LineOfCode(
						String.format("medium%d(%s);",
							path.get(opt.next), argStr), 2));

				choiceFrom.add(new LineOfCode(
						String.format("<!%s;t%s_%d> l%2$s_%d_%d;",
							opt.type, entry.fromStr,
							idxTypes.get(entry.fromStr).get(opt.next),
							fromTypeNr, i), 1));
				choiceTo.add(new LineOfCode(
						String.format("<?%s;t%s_%d> l%2$s_%d_%d;",
							opt.type, entry.toStr,
							idxTypes.get(entry.toStr).get(opt.next),
							toTypeNr, i), 1));
			}

			else
			{
				Map<Integer,Integer> newPath = new HashMap<>(path);
				newPath.put(idx, mediumNr);

				// Copy the nr of types for non-senders/-recipients.
				newNrsOfTypes = new HashMap<>(nrsOfTypes);

				// Call the next medium.
				medium.add(new LineOfCode(
						String.format("medium%d(%s);",
							nrOfMediums, argStr), 2));

				// Unset the next types for the sender and reciever, since if
				// there is no next we want to know.
				nextTypes.remove(entry.fromStr);
				nextTypes.remove(entry.toStr);

				// Follow the branch.
				Pair<Integer,Integer> res = buildCC0Templ(
						entries, opt.next, roles, argStr,
						newPath, idxTypes, newNrsOfTypes, nextTypes,
						typedefs, choices, mediums, mediumDecs,
						nrOfVars, nrOfMediums);

				nrOfVars = res.left;
				nrOfMediums = res.right;

				// Update the nr of types for sender and recipient.
				int newFromNrOfTypes = newNrsOfTypes.get(entry.fromStr);
				nrsOfTypes.put(entry.fromStr, newFromNrOfTypes);
				int newToNrOfTypes = newNrsOfTypes.get(entry.toStr);
				nrsOfTypes.put(entry.toStr, newToNrOfTypes);

				String fromCont = "";
				if (nextTypes.containsKey(entry.fromStr))
				{
					fromCont = String.format("t%s_%d",
							entry.fromStr, nextTypes.get(entry.fromStr));
				}
				String toCont = "";
				if (nextTypes.containsKey(entry.toStr))
				{
					toCont = String.format("t%s_%d",
							entry.toStr, nextTypes.get(entry.toStr));
				}

				choiceFrom.add(new LineOfCode(
						String.format("<!%s;%s> l%s_%d_%d;",
							opt.type, fromCont, entry.fromStr, fromTypeNr, i),
						1));
				choiceTo.add(new LineOfCode(
						String.format("<?%s;%s> l%s_%d_%d;",
							opt.type, toCont, entry.toStr, toTypeNr, i), 1));
			}

			medium.add(new LineOfCode(
					"break;", 2));
		}

		medium.add(new LineOfCode("}", 1));
		medium.add(new LineOfCode("}", 0));
		choiceFrom.add(new LineOfCode("};", 0));
		choiceTo.add(new LineOfCode("};", 0));

		// Update with the last taken branch.
		if (newNrsOfTypes != null)
		{
			nrsOfTypes.putAll(newNrsOfTypes);
		}

		nextTypes.put(entry.fromStr, fromTypeNr);
		nextTypes.put(entry.toStr, toTypeNr);

		String params = "";
		for (int i = 0; i < roles.length; i ++)
		{
			if (i > 0)
			{
				params += ",";
			}

			// Only if something has happened to the role is the channel still
			// available.
			if (nrsOfTypesBeforeRec.get(roles[i]) != nrsOfTypes.get(roles[i]))
			{
				params += String.format("t%s_%d $%1$s",
						roles[i], nrsOfTypesBeforeRec.get(roles[i]));
			}
			else
			{
				params += String.format("<> $%s", roles[i]);
			}
		}
		medium.add(0, new LineOfCode(
				String.format("void medium%d(%s) {", mediumNr, params), 0));
		mediumDecs.put(mediumNr, new LineOfCode(
				String.format("void medium%d(%s);", mediumNr, params), 0));

		return new Pair<>(nrOfVars, nrOfMediums);
	}

	@Override
	public String toDot()
	{
		return this.init.toDot();
	}

	@Override
	public String toAut()
	{
		return this.init.toAut();
	}

	@Override
	public String toString()
	{
		return this.init.toString();
	}

	public String toCanonProtocol()
	{
		List<CanonProtocolEntry> entries = new ArrayList<>();
		int initIdx = buildCanonProtocol(this.init, entries, new HashMap<>());

		return toCanonProtocol(entries, initIdx, new HashSet<>(), new HashSet<>());
	}

	public String toCC0Templ()
	{
		List<CanonProtocolEntry> entries = new ArrayList<>();
		int initIdx = buildCanonProtocol(this.init, entries, new HashMap<>());
		String[] roles = canonToRoleStrs(entries, initIdx, new HashSet<>())
			.toArray(new String[0]);

		Map<String,Map<Integer,LineOfCode>> typedefs
			= new HashMap<>();
		Map<String,Map<Integer,List<LineOfCode>>> choices
			= new HashMap<>();
		Map<String,Map<Integer,Integer>> idxTypes = new HashMap<>();
		Map<String,Integer> nrsOfTypes = new HashMap<>();
		String argStr = "";
		for (int i = 0; i < roles.length; i ++)
		{
			typedefs.put(roles[i], new HashMap<>());
			choices.put(roles[i], new HashMap<>());
			idxTypes.put(roles[i], new HashMap<>());
			nrsOfTypes.put(roles[i], 0);

			if (i > 0)
			{
				argStr += ",";
			}
			argStr += String.format("$%s", roles[i]);
		}

		Map<Integer,List<LineOfCode>> mediums = new HashMap<>();
		Map<Integer,LineOfCode> mediumDecs = new HashMap<>();

		Pair<Integer,Integer> linesRes = buildCC0Templ(
				entries, initIdx, roles, argStr,
				new HashMap<>(), // empty path to start with.
				idxTypes, nrsOfTypes,
				new HashMap<>(), // we don't have to know this here.
				typedefs, choices, mediums, mediumDecs, 0, 0);
		int nrOfMediums = linesRes.right;

		String out = "";

		for (int i = 0; i < roles.length; i ++)
		{
			int nrOfTypes = nrsOfTypes.get(roles[i]);
			Map<Integer,LineOfCode> roleTypedefs = typedefs.get(roles[i]);
			Map<Integer,List<LineOfCode>> roleChoices = choices.get(roles[i]);

			for (int j = nrOfTypes-1; j >= 0; j --)
			{
				out += roleTypedefs.get(j).toString() + "\n";
			}
			out += "\n";
			for (int j = nrOfTypes-1; j >= 0; j --)
			{
				out += linesOfCodeToString(roleChoices.get(j));
			}
			out += "\n"
				+ String.format("t%s_0 $%1$s %1$s() {\n}\n\n", roles[i]);
		}

		for (int i = 0; i < nrOfMediums ; i ++)
		{
			out += mediumDecs.get(i).toString() + "\n";
		}
		out += "\n";
		for (int i = nrOfMediums-1; i >= 0; i --)
		{
			out += linesOfCodeToString(mediums.get(i)) + "\n";
		}

		out += "void medium(";
		for (int i = 0; i < roles.length; i ++)
		{
			if (i > 0)
			{
				out += ", ";
			}
			out += String.format("t%s_0 $%1$s", roles[i]);
		}
		out += ") {\n"
			+ "    medium0(" + argStr + ");\n"
			+ "}\n\n";

		out += "void " + this.proto.getLastElement() + "() {\n";
		String chanArgs = "";
		for (int i = 0; i < roles.length; i ++)
		{
			if (i > 0)
			{
				chanArgs += ", ";
			}
			out += String.format("	  t%s_0 $%1$s = %1$s();\n", roles[i]);
			chanArgs += "$" + roles[i];
		}
		out += "	medium(" + chanArgs + ");\n"
			+  "}";

		return out;
	}

	private class CanonProtocolOption
	{
		public final String type;
		public final int next;

		public CanonProtocolOption(Payload type, int next)
		{
			if (type.toString(false) == "")
			{
				this.type = "unit";
			}
			else
			{
				this.type = type.toString(false);
			}
			this.next = next;
		}
	}

	private class CanonProtocolEntry
	{
		public final Role from;
		public final String fromStr;
		public final Role to;
		public final String toStr;
		public List<CanonProtocolOption> options;

		public CanonProtocolEntry(Role from, Role to)
		{
			this.from = from;
			this.fromStr = from.toString();
			this.to = to;
			this.toStr = to.toString();
			this.options = new ArrayList<>();
		}
	}

	private class LineOfCode
	{
		public String code;
		private int depth;
		private static final int tabwidth = 4;

		public LineOfCode(String code, int depth)
		{
			this.code = code;
			this.depth = depth;
		}

		public void increaseDepth()
		{
			this.depth = this.depth + 1;
		}

		public String toString()
		{
			String out = "";
			for (int i = 0; i < this.depth; i ++) {
				for (int j = 0; j < this.tabwidth; j ++) {
					out += " ";
				}
			}
			out += this.code;
			return out;
		}
	}

	private String linesOfCodeToString(List<LineOfCode> lines)
	{
		String out = "";
		for (int i = 0; i < lines.size(); i ++)
		{
			out += lines.get(i).toString() + "\n";
		}
		return out;
	}

	private class Pair<Tl, Tr>
	{
		public Tl left;
		public Tr right;

		public Pair(Tl left, Tr right)
		{
			this.left = left;
			this.right = right;
		}
	}
}
