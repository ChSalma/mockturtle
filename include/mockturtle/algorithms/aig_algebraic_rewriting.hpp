/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });   
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
         return true;
    /* TODO: add more rules here... */
    if (try_three_layer_distributivity ( n ))
       return true;
    //if ( try_absorption( n ) )
      //return true;
    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    //check critical path and number of fanout
    if ( ntk.is_on_critical_path( n )  && ntk.fanin_size( n ) == 2 )
    {
      std::vector<signal> fanin_signal;
      std::vector<node> fanin_node;
      std::vector<node> child_node;
      std::vector<signal> child_signal;

      ntk.foreach_fanin( n, [&]( signal const& s )
                         {
                           fanin_node.push_back( ntk.get_node( s ) );
                           fanin_signal.push_back( s );
                         } );
      //find critical fanin and check that it is not complemented
      //apply associativty only if level difference is at least 2
      if (ntk.level( fanin_node[1] ) >  ntk.level( fanin_node[0] ))
        {
          std::swap( fanin_node[1], fanin_node[0] );
          std::swap( fanin_signal[1], fanin_signal[0] );
      }
      if ( ntk.level( fanin_node[0] ) > ( ntk.level( fanin_node[1] ) + 1 ) && !ntk.is_complemented( fanin_signal[0] ) )
      {
        ntk.foreach_fanin( fanin_node[0], [&]( signal s )
                           {
                             child_node.push_back( ntk.get_node( s ) );
                             child_signal.push_back( s );
                           } );
        if (ntk.level( child_node[1] ) > ntk.level( child_node[0] ))
          {
            std::swap( child_node[1], child_node[0] );
            std::swap( child_signal[1], child_signal[0] );
          }
        if ( ntk.level( child_node[0] ) > ntk.level( child_node[1] ) )
        {
          exchange_f1_f2( fanin_signal[1], child_signal[1], child_signal[0], n );
          return true;
        }
        else
          return false;
      }
      else
        return false;
    }
    return false;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n )
  {
    // check critical path condition and fanin size
    if ( ntk.is_on_critical_path( n ) && ntk.fanin_size( n ) == 2 )
    {
      std::vector<signal> fanin_signal;
      std::vector<node> fanin_node;
      ntk.foreach_fanin( n, [&]( signal const& s )
                         {
                           fanin_node.push_back( ntk.get_node( s ) );
                           fanin_signal.push_back( s );
                         } );
      if (!ntk.is_complemented(fanin_signal[0]) && !ntk.is_complemented(fanin_signal[1]))
          return try_distributivity_and_or_top( n, fanin_signal[0], fanin_signal[1], fanin_node[0], fanin_node[1], false );
      else if (ntk.is_complemented(fanin_signal[0]) && ntk.is_complemented(fanin_signal[1]))
        return try_distributivity_and_or_top( n, fanin_signal[0], fanin_signal[1], fanin_node[0], fanin_node[1], true );
      else return false;
    }
    return false;
  }

    bool try_distributivity_and_or_top(node n, signal fanin0_signal, signal fanin1_signal, node fanin0_node, node fanin1_node, bool flag_and0_or1)
    {
      std::vector<node> child0_node;
      std::vector<signal> child0_signal;
      std::vector<node> child1_node;
      std::vector<signal> child1_signal;

      ntk.foreach_fanin( fanin0_node, [&]( signal const& s )
                         {
                           child0_node.push_back( ntk.get_node( s ) );
                           child0_signal.push_back( s );
                         } );
      ntk.foreach_fanin( fanin1_node, [&]( signal const& s )
                           {
                             child1_node.push_back( ntk.get_node( s ) );
                             child1_signal.push_back( s );
                           } );
      //check fanin size
      if ( ntk.fanin_size( fanin0_node ) < 2 || ntk.fanin_size( fanin1_node ) < 2 )
        return false;

      if (child0_signal[0] == child1_signal[0] && ntk.is_on_critical_path(child0_node[0]))
        {
        distributivity_modify_network( n, child0_node[0], child0_signal[0], child0_signal[1], child1_signal[1], flag_and0_or1 );
          return true;
        }
      else if (child0_signal[0] == child1_signal[1] && ntk.is_on_critical_path(child0_node[0]))
        {
        distributivity_modify_network( n, child0_node[0], child0_signal[0], child0_signal[1], child1_signal[0], flag_and0_or1 );
          return true;
        
      }
      else if (child0_signal[1] == child1_signal[0] && ntk.is_on_critical_path(child0_node[1]))
        {
        distributivity_modify_network( n, child0_node[1], child0_signal[1], child0_signal[0], child1_signal[1], flag_and0_or1 );
          return true;
        
      }
    else if (child0_signal[1] == child1_signal[1] && ntk.is_on_critical_path(child0_node[1]))
      {
      distributivity_modify_network( n, child0_node[1], child0_signal[1], child0_signal[0], child1_signal[0], flag_and0_or1 );
        return true;
      }
    return false;
          
    }

    bool try_three_layer_distributivity(node n)
    {
      // check critical path condition and fanin size
      if ( ntk.is_on_critical_path( n ) && ntk.fanin_size( n ) == 2 )
      {
        std::vector<signal> fanin_signal;
        std::vector<node> fanin_node;
        ntk.foreach_fanin( n, [&]( signal const& s )
                           {
                             fanin_node.push_back( ntk.get_node( s ) );
                             fanin_signal.push_back( s );
                           } );
        if ( ntk.level( fanin_node[1] ) > ntk.level( fanin_node[0] ) )
        {
          std::swap( fanin_node[1], fanin_node[0] );
          std::swap( fanin_signal[1], fanin_signal[0] );
        }
        //requires a difference of level of minimum 3 between the fanins
        //critical path has to be complemented
        if ( ntk.level( fanin_node[0] ) > ( ntk.level( fanin_node[1] ) + 2 ) && ntk.is_complemented( fanin_signal[0] ) )
        {
          std::vector<signal> child_signal;
          std::vector<node> child_node;
          if ( ntk.fanin_size( fanin_node[0] ) < 2 )
            return false;
          ntk.foreach_fanin( fanin_node[0], [&]( signal const& s )
                             {
                               child_node.push_back( ntk.get_node( s ) );
                               child_signal.push_back( s );
                             } );

          if ( ntk.level( child_node[1] ) > ntk.level( child_node[0] ) )
          {
            std::swap( child_node[1], child_node[0] );
            std::swap( child_signal[1], child_signal[0] );
          }
          //requires a difference of level of minimum 2 between the children
          //critical path has to be complemented
          if ( ntk.level( child_node[0] ) > ( ntk.level( child_node[1] ) + 1 ) && ntk.is_complemented( child_signal[0] ) )
          {
            std::vector<signal> gchild_signal;
            std::vector<node> gchild_node;
            if ( ntk.fanin_size( child_node[0] ) < 2 )
              return false;
            ntk.foreach_fanin( child_node[0], [&]( signal const& s )
                               {
                                 gchild_node.push_back( ntk.get_node( s ) );
                                 gchild_signal.push_back( s );
                               } );
            if ( ntk.level( gchild_node[1] ) > ntk.level( gchild_node[0] ) )
            {
              std::swap( gchild_node[1], gchild_node[0] );
              std::swap( gchild_signal[1], gchild_signal[0] );
            }
            if ( ntk.level( gchild_node[0] ) > ( ntk.level( gchild_node[1] ) + 1 ) )
            {
              three_layer_modify_network( n, gchild_signal[1], child_signal[1], fanin_signal[1], gchild_signal[0] );
              return true;
            }
            else
              return false;
          }
        }
        else
          return false;
      }
      else
        return false;
      return false;
    }

  bool try_absorption( node n )
  {
    /* TODO */
    if ( ntk.is_on_critical_path( n ) && ntk.fanin_size( n ) == 2 )
    {
      std::vector<signal> fanin_signal;
      std::vector<node> fanin_node;
      ntk.foreach_fanin( n, [&]( signal const& s )
                         {
                           fanin_node.push_back( ntk.get_node( s ) );
                           fanin_signal.push_back( s );
                         } );
      if ( ntk.level( fanin_node[1] ) > ntk.level( fanin_node[0] ) )
      {
        std::swap( fanin_node[1], fanin_node[0] );
        std::swap( fanin_signal[1], fanin_signal[0] );
      }
      if ( ntk.level( fanin_node[0] ) > ( ntk.level( fanin_node[1] ) ) && ntk.is_complemented( fanin_signal[0] ) )
      {

        std::vector<signal> child_signal;
        std::vector<node> child_node;
        if ( ntk.fanin_size( fanin_node[0] ) < 2 )
          return false;
        ntk.foreach_fanin( fanin_node[0], [&]( signal const& s )
                           {
                             child_node.push_back( ntk.get_node( s ) );
                             child_signal.push_back( s );
                           } );
        if (( child_node[0] == fanin_node[1] && child_signal[0] != fanin_signal[1] )
          || ( child_node[1] == fanin_node[1] && child_signal[1] != fanin_signal[1] ))
          {
            if (ntk.is_complemented(fanin_signal[1]))
                ntk.substitute_node( n, !fanin_signal[1] );
            else 
                ntk.substitute_node( n, fanin_signal[1] );
            return true;
          }
        else
          return false;
      }
      else return false;


                  

    }
    else return false;
  }

  /* Exchange signals with complementary of signal conservation*/
  void exchange_f1_f2( signal const& non_critical_fanin, signal const& non_critical_child, signal const& critical_child, node const& node )
  {
    signal new_fanin_node = ntk.create_and( non_critical_fanin, non_critical_child );
    signal node_signal = ntk.create_and( new_fanin_node, critical_child );
    ntk.substitute_node( node, node_signal );
  }
  /*Modification of the network for the distributivity*/
  void distributivity_modify_network( node n, node common_node, signal common_signal, signal signal0, signal signal1, bool flag_and0_or1 )
  {
    if ( !flag_and0_or1 )
    {
      signal new_fanin_signal = ntk.create_and( signal0, signal1 );
      signal new_out_node = ntk.create_and( new_fanin_signal, common_signal );
      ntk.substitute_node( n, new_out_node );
    }
    else
    {
      signal new_fanin_signal = ntk.create_and( !signal0, !signal1 );
      signal new_out_node = ntk.create_and( !new_fanin_signal, common_signal );
      ntk.substitute_node( n, !new_out_node );
    }
  }
  void three_layer_modify_network( node n, signal non_critical_gchild, signal non_critical_child, signal non_critical_fanin, signal critical_signal)
  {
    signal out1 = ntk.create_and( non_critical_gchild, non_critical_fanin );
    signal out2 = ntk.create_and( critical_signal, out1 );
    signal out3 = ntk.create_and( !non_critical_child, non_critical_fanin );
    signal out4 = ntk.create_and( !out2, !out3);
    ntk.substitute_node( n, !out4 );
  }

private:
  Ntk& ntk;
};

} // namespace detail
/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */