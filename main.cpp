/*
* Copyright (C) 2012 Michael Hansen (mihansen@indiana.edu)
* 
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
* 
* The above copyright notice and this permission notice shall be included in all
* copies or substantial portions of the Software.
* 
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*/

#include <iostream>
#include <string>
#include <cmath>
#include <cassert>
#include <map>
#include <limits>
#include <stack>
#include <boost/foreach.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/iteration_macros.hpp>

/* Utility Functions */

double log2(double x) {
  return log10(x) / log10(2.0);
}

double integer_length(double n) {
  return log2(n) + log2(log2(n + 1)) + 1;
}

template <typename Graph, typename PredecessorMap, typename ModuleMap>
void make_predecessor_map
(const Graph& g,
 PredecessorMap& pred_map,
 ModuleMap& mod_map) {

  // Initialize property map
  BGL_FORALL_VERTICES_T(v, g, Graph) {
    boost::put(pred_map, v, boost::graph_traits<Graph>::null_vertex());
  }

  BGL_FORALL_EDGES_T(e, g, Graph) {
    if (boost::get(mod_map, source(e, g))) {
      boost::put(pred_map, target(e, g), source(e, g));
    }
  }
}

/* Computes the Lutz complexity of a graph.
 *
 * See Lutz, 2002 "Recovering high-level structure of software systems using a
 * minimum description length principle" for details.
 *
 * Parameters
 * ==========
 * Graph& g - directed graph of dependencies
 *
 * ModuleMap& mod_map - map from vertices to boolean values indicating if the
 *                      given vertex is considered a module or not.
 *
 * PredecessorMap& pred_map - map from vertices to parent modules (use
 *                            make_predecessor_map utility function).
 *
 * VertexIndexMap& vindex_map - map from vertices to unique integers.
 *
 * */
template<typename Graph,
  typename ModuleMap,
  typename PredecessorMap,
  typename VertexIndexMap>
double lutz_complexity
(const Graph& g, 
 const ModuleMap& mod_map,
 const PredecessorMap& pred_map,
 const VertexIndexMap& vindex_map) {

  typedef typename boost::graph_traits<Graph>::vertex_descriptor Vertex;
  typedef typename boost::graph_traits<Graph>::vertices_size_type VertexSize;

  double complexity = 0;
  VertexSize vertex_count = boost::num_vertices(g);
  VertexSize up_idx = vertex_count;

  assert(vertex_count > 0);

  // For each module in g
  // \sum_{m \in \mathcal{M}}
  BGL_FORALL_VERTICES_T(mod_m, g, Graph) {
    if (!boost::get(mod_map, mod_m)) {
      continue;
    }

    Vertex node_n;
    VertexSize num_modules = 0, num_nodes = 0;
    VertexSize freq_m[vertex_count + 1];
    freq_m[up_idx] = 1;

    VertexSize freq_m_total = 1; // One for "up"

    // For every node in the module
    BGL_FORALL_ADJ_T(mod_m, node_n, g, Graph) {

      VertexSize node_n_idx = vindex_map[node_n];

      // All code names must be sent at least once
      freq_m[node_n_idx] = 1;
      ++freq_m_total;

      if (boost::get(mod_map, node_n)) {
        ++num_modules;
      }
      else {
        ++num_nodes;

        // For every out-going edge of this node
        // \sum_{n \in N_m}{\sum_{n' \in out N(n)}{l(relD(n, lca(n, n'))}}
        BGL_FORALL_OUTEDGES_T(node_n, e_out_n, g, Graph) {

          Vertex node_out_n = target(e_out_n, g);
          VertexSize node_out_n_idx = boost::get(vindex_map, node_out_n);

          // Determine least common ancestor
          std::stack<VertexSize> n_preds, out_n_preds;
          VertexSize pred_n = boost::get(pred_map, node_n);
          VertexSize pred_out_n = boost::get(pred_map, node_out_n);

          while (pred_n != boost::graph_traits<Graph>::null_vertex()) {
            n_preds.push(boost::get(vindex_map, pred_n));
            pred_n = boost::get(pred_map, pred_n);
          }

          while (pred_out_n != boost::graph_traits<Graph>::null_vertex()) {
            out_n_preds.push(boost::get(vindex_map, pred_out_n));
            pred_out_n = boost::get(pred_map, pred_out_n);
          }

          assert(!n_preds.empty() && !out_n_preds.empty());

          VertexSize mod_lca_idx = vertex_count;
          while (!n_preds.empty() && !out_n_preds.empty()) {
            if (n_preds.top() != out_n_preds.top()) {
              break;
            }

            mod_lca_idx = n_preds.top();
            n_preds.pop();
            out_n_preds.pop();
          }

          assert(mod_lca_idx < vertex_count);

          // Remaining distance to root is relative distance to lca (from n)
          VertexSize dist_n_lca = 0;
          
          while (!n_preds.empty()) {
            ++dist_n_lca;
            n_preds.pop();
          }

          if (dist_n_lca > 0) {
            freq_m[up_idx] += dist_n_lca;
            freq_m_total += dist_n_lca;
            complexity += integer_length(dist_n_lca);
          }
        }

      } // if module or node

      BGL_FORALL_EDGES_T(e, g, Graph) {
        if (boost::get(vindex_map, target(e, g)) == node_n_idx) {
          ++(freq_m[node_n_idx]);
          ++freq_m_total;
        }
      }

    } // for all nodes adjacent to module

    // Add in node codes
    BGL_FORALL_ADJ_T(mod_m, node_n, g, Graph) {
      double node_freq = (double)freq_m[vindex_map[node_n]];
      assert(node_freq > 0);

      double node_code = -log2(node_freq / (double)freq_m_total);
      complexity += integer_length(node_code);
      complexity += node_freq * node_code;
    }

    // Add in up code
    double up_freq = (double)freq_m[up_idx];
    assert(up_freq > 0);

    double up_code = -log2(up_freq / (double)freq_m_total);
    complexity += integer_length(up_code);
    complexity += up_freq * up_code;

    // l(|N_m| + 1) + l(|M_m) + 1)
    complexity += integer_length(num_modules + 1) +
      integer_length(num_nodes + 1);

  } // for all modules in graph

  return (complexity);
}

/* Computes the Lutz complexity of a graph. Assumes the graph g has a
 * vertex_index property map.
 *
 * See Lutz, 2002 "Recovering high-level structure of software systems using a
 * minimum description length principle" for details.
 *
 * Parameters
 * ==========
 * Graph& g - directed graph of dependencies
 *
 * ModuleMap& mod_map - map from vertices to boolean values indicating if the
 *                      given vertex is considered a module or not.
 *
 * PredecessorMap& pred_map - map from vertices to parent modules (use
 *                            make_predecessor_map utility function).
 *
 * */
template<typename Graph,
  typename ModuleMap,
  typename PredecessorMap>
inline double lutz_complexity
(const Graph& g,
 const ModuleMap& mod_map,
 const PredecessorMap& pred_map) {
  return lutz_complexity(g, mod_map, pred_map,
                         boost::get(boost::vertex_index, g));
}

/* Computes the Lutz complexity of a graph. Creates the module predecessor map
 * using the make_predecessor_map utility function. Assumes the graph g has a
 * vertex_index property map.
 *
 * See Lutz, 2002 "Recovering high-level structure of software systems using a
 * minimum description length principle" for details.
 *
 * Parameters
 * ==========
 * Graph& g - directed graph of dependencies
 *
 * ModuleMap& mod_map - map from vertices to boolean values indicating if the
 *                      given vertex is considered a module or not.
 *
 * */
template<typename Graph,
  typename ModuleMap>
inline double lutz_complexity
(const Graph& g,
 const ModuleMap& mod_map) {

  typedef typename boost::graph_traits<Graph>::vertex_descriptor Vertex;
  typedef std::map<Vertex, Vertex> PredecessorMapBase;

  PredecessorMapBase pred_map_base;
  boost::associative_property_map<PredecessorMapBase> pred_map(pred_map_base);
  make_predecessor_map(g, pred_map, mod_map);

  return lutz_complexity(g, mod_map, pred_map);
}

int main(int argc, char** argv) {

  typedef std::pair<int, int> Edge;

  // Example models from Lutz, 2002
  enum components {
    Main, User, Control, Family,
    State, Memory, File, Computer,
    Directory, FileTable, Inode,
    InodeTable, FreeInode, FileIO,
    Device, InodeGlobals, Disk, Tty,
    System, Panic,

    M0, M1, M2, M3, M4, M5, M6,
    M7, M8, M9, M10, M11, M12, M13,
    M14, M15, M16, M17, M18, M19, M20
  };

  std::string names[] = {
    "Main", "User", "Control", "Family",
    "State", "Memory", "File", "Computer",
    "Directory", "FileTable", "Inode",
    "InodeTable", "FreeInode", "FileIO",
    "Device", "InodeGlobals", "Disk", "Tty",
    "System", "Panic",

    "M0", "M1", "M2", "M3", "M4", "M5", "M6",
    "M7", "M8", "M9", "M10", "M11", "M12", "M13",
    "M14", "M15", "M16", "M17", "M18", "M19", "M20"
  };

  bool is_module[] = {
    false, false, false, false,
    false, false, false, false,
    false, false, false,
    false, false, false,
    false, false, false, false,
    false, false,

    true, true, true, true,
    true, true, true, true,
    true, true, true, true,
    true, true, true, true,
    true, true, true, true, true
  };


  Edge edge_list[] = {
    Edge(Main, User), Edge(Main, Control),

    Edge(User, Family), Edge(User, File), Edge(User, Panic),
    Edge(User, System), Edge(User, State), Edge(User, Memory),
    Edge(User, Computer),

    Edge(Control, Family), Edge(Control, File), Edge(Control, Tty),
    Edge(Control, Panic), Edge(Control, System),

    Edge(Family, State),

    Edge(State, Memory), Edge(State, Computer), Edge(State, File),
    Edge(State, System),

    Edge(Memory, Computer), Edge(Memory, File), Edge(Memory, System),

    Edge(File, Directory), Edge(File, FileTable), Edge(File, Inode),
    Edge(File, System), Edge(File, Panic),

    Edge(FileTable, Inode),

    Edge(Inode, InodeTable), Edge(Inode, FileIO),
    Edge(Inode, Device), Edge(Inode, Panic), Edge(Inode, FreeInode),
    Edge(Inode, InodeGlobals), Edge(Inode, System), 

    Edge(InodeTable, InodeGlobals), Edge(InodeTable, FreeInode),
    Edge(InodeTable, FileIO), Edge(InodeTable, Panic),

    Edge(FreeInode, FileIO), Edge(FreeInode, InodeGlobals), 

    Edge(FileIO, InodeGlobals), Edge(FileIO, Device), 
    Edge(FileIO, Panic),

    Edge(InodeGlobals, System), Edge(InodeGlobals, Panic),

    Edge(Device, System), Edge(Device, Disk), Edge(Device, Tty),

    Edge(Directory, Inode), Edge(Directory, Panic)
  };

  typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS,
          boost::property<boost::vertex_index_t, unsigned int> > Graph;

  Graph flat_model, bunch_model, lutz_model;

  // Flat
  for (int i = 0; i < 20; ++i) {
    boost::add_edge(M0, i, flat_model);
  }

  // BUNCH
  boost::add_edge(M0, M1, bunch_model);
  boost::add_edge(M0, M2, bunch_model);
  boost::add_edge(M0, M3, bunch_model);
  boost::add_edge(M0, M4, bunch_model);
  boost::add_edge(M0, M5, bunch_model);

  boost::add_edge(M1, Main, bunch_model);
  boost::add_edge(M1, Control, bunch_model);
  boost::add_edge(M1, Family, bunch_model);

  boost::add_edge(M2, User, bunch_model);
  boost::add_edge(M2, State, bunch_model);
  boost::add_edge(M2, Memory, bunch_model);
  boost::add_edge(M2, Computer, bunch_model);

  boost::add_edge(M3, File, bunch_model);
  boost::add_edge(M3, FileTable, bunch_model);
  boost::add_edge(M3, Directory, bunch_model);
  boost::add_edge(M3, Inode, bunch_model);
  boost::add_edge(M3, Panic, bunch_model);

  boost::add_edge(M4, Device, bunch_model);
  boost::add_edge(M4, Tty, bunch_model);
  boost::add_edge(M4, Disk, bunch_model);
  boost::add_edge(M4, System, bunch_model);

  boost::add_edge(M5, InodeTable, bunch_model);
  boost::add_edge(M5, FreeInode, bunch_model);
  boost::add_edge(M5, FileIO, bunch_model);
  boost::add_edge(M5, InodeGlobals, bunch_model);

  // Lutz
  boost::add_edge(M0, M1, lutz_model);
  boost::add_edge(M0, M2, lutz_model);
  boost::add_edge(M0, M3, lutz_model);
  boost::add_edge(M0, M4, lutz_model);

  boost::add_edge(M0, Main, lutz_model);
  boost::add_edge(M0, Control, lutz_model);
  boost::add_edge(M0, User, lutz_model);
  boost::add_edge(M0, Family, lutz_model);

  boost::add_edge(M1, State, lutz_model);
  boost::add_edge(M1, Memory, lutz_model);
  boost::add_edge(M1, Computer, lutz_model);

  boost::add_edge(M2, File, lutz_model);
  boost::add_edge(M2, FileTable, lutz_model);
  boost::add_edge(M2, Directory, lutz_model);

  boost::add_edge(M3, InodeTable, lutz_model);
  boost::add_edge(M3, InodeGlobals, lutz_model);
  boost::add_edge(M3, FileIO, lutz_model);
  boost::add_edge(M3, Inode, lutz_model);
  boost::add_edge(M3, FreeInode, lutz_model);

  boost::add_edge(M4, System, lutz_model);
  boost::add_edge(M4, Disk, lutz_model);
  boost::add_edge(M4, Device, lutz_model);
  boost::add_edge(M4, Panic, lutz_model);
  boost::add_edge(M4, Tty, lutz_model);

  const int num_models = 3;
  Graph* models[] = { &flat_model, &bunch_model, &lutz_model };
  std::string model_names[] = {
    "flat model", "BUNCH model", "Lutz example model"
  };

  typedef boost::graph_traits<Graph>::vertex_descriptor Vertex;
  typedef boost::graph_traits<Graph>::vertices_size_type VertexSize;
  const int V = 41;

  std::map<Vertex, bool> mod_std_map;
  boost::associative_property_map<std::map<Vertex, bool> > mod_map(mod_std_map);

  for (int i = 0; i < V; ++i) {
    put(mod_map, i, is_module[i]);
  }

  // Compute the Lutz complexity of each model
  std::cout << "Lutz complexities of various models (see Lutz, 2002)" << std::endl;
  for (int i = 0; i < num_models; ++i) {
    Graph* model = models[i];
    std::pair<int, int> e;

    BOOST_FOREACH(e, edge_list) {
      boost::add_edge(e.first, e.second, *model);
      boost::add_edge(e.second, e.first, *model);
    }

    std::cout << model_names[i] << ": " << lutz_complexity(*model, is_module) << std::endl;
  }

  return (0);
}

