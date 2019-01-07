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

	private class CanonProtocolOption
	{
		public final Payload type;
		public final int next;

		public CanonProtocolOption(Payload type, int next)
		{
			this.type = type;
			this.next = next;
		}
	}

	private class CanonProtocolEntry
	{
		public final Role from;
		public final Role to;
		public List<CanonProtocolOption> options;

		public CanonProtocolEntry(Role from, Role to)
		{
			this.from = from;
			this.to = to;
			this.options = new ArrayList<>();
		}
	}

	public String toCanonProtocol()
	{
		List<CanonProtocolEntry> entries = new ArrayList<>();
		int initIdx = buildCanonProtocol(this.init, entries, new HashMap<>());

		return toCanonProtocol(entries, initIdx, new HashSet<>(), new HashSet<>());
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
			out += i + "<" + option.type.toString() + ">.";

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
}
