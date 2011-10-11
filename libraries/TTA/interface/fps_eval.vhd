library ieee;
use ieee.std_logic_1164.all;

entity fps_eval is
  generic (
    period : in integer
    );
  port (
    rst          : in  std_logic;
    clk          : in  std_logic;
    top_frame    : in  std_logic;
    segment7     : out std_logic_vector(6 downto 0);
    segment7_sel : out std_logic_vector(2 downto 0)
    );
end fps_eval;


architecture rtl_fps_eval of fps_eval is
  signal top_ms     : std_logic;
  signal top_s      : std_logic;
  --
  signal count_u    : std_logic_vector(15 downto 0);
  signal top_u      : std_logic;
  signal count_t    : std_logic_vector(15 downto 0);
  signal top_t      : std_logic;
  signal count_h    : std_logic_vector(15 downto 0);
  --
  signal segment7_u : std_logic_vector(6 downto 0);
  signal segment7_t : std_logic_vector(6 downto 0);
  signal segment7_h : std_logic_vector(6 downto 0);
begin
  
  counter_ms : work.counter
    generic map (
      nb_count => 1000*1000/period)
    port map (
      rst   => rst,
      clk   => clk,
      valid => '1',
      top   => top_ms);

  counter_s : work.counter
    generic map (
      nb_count => 1000)
    port map (
      rst   => rst,
      clk   => clk,
      valid => top_ms,
      top   => top_s);

  counter_u : work.counter
    generic map (
      nb_count => 10)
    port map (
      rst   => rst,
      clk   => clk,
      count => count_u,
      valid => top_frame,
      top   => top_u);

  counter_t : work.counter
    generic map (
      nb_count => 10)
    port map (
      rst   => rst,
      clk   => clk,
      count => count_t,
      valid => top_u,
      top   => top_t);

  counter_h : work.counter
    generic map (
      nb_count => 10)
    port map (
      rst   => rst,
      clk   => clk,
      count => count_h,
      valid => top_t);

  segment_display_conv_u : work.segment_display_conv
    port map (
      clk      => clk,
      bcd      => count_u(3 downto 0),
      segment7 => segment7_u);

  segment_display_conv_t : work.segment_display_conv
    port map (
      clk      => clk,
      bcd      => count_t(3 downto 0),
      segment7 => segment7_t);

  segment_display_conv_h : work.segment_display_conv
    port map (
      clk      => clk,
      bcd      => count_h(3 downto 0),
      segment7 => segment7_h);

  segment_display_sel_component : work.segment_display_sel
    port map (
      clk          => clk,
      rst          => rst,
      segment7_u   => segment7_u,
      segment7_t   => segment7_t,
      segment7_h   => segment7_h,
      segment7     => segment7,
      segment7_sel => segment7_sel);

end rtl_fps_eval;



