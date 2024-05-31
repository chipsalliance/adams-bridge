// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//======================================================================
//
// twiddle_rom.sv
// --------
// ROM contains twiddle factors for NTT and INTT
// 
//
//======================================================================

module ntt_twiddle_lookup 
    import ntt_defines_pkg::*;
#(
    parameter ADDR_WIDTH = 7,
    parameter DATA_WIDTH = 23
)
(

    input mode_t mode,
    input wire [ADDR_WIDTH-1:0] raddr,
    output logic [(3*DATA_WIDTH)-1:0] rdata
);

reg [(3*DATA_WIDTH)-1:0] ntt_twiddle_mem  [84:0];
reg [(3*DATA_WIDTH)-1:0] intt_twiddle_mem [84:0];

always_comb begin
    rdata = (mode == ct) ? ntt_twiddle_mem[raddr] : (mode == gs) ? intt_twiddle_mem[raddr] : 'h0;
end

logic [(3*DATA_WIDTH)-1:0] zeta3_zeta2_zeta1;


logic [(3*DATA_WIDTH)-1:0] zeta9_zeta8_zeta4;
logic [(3*DATA_WIDTH)-1:0] zeta11_zeta10_zeta5;
logic [(3*DATA_WIDTH)-1:0] zeta13_zeta12_zeta6;
logic [(3*DATA_WIDTH)-1:0] zeta15_zeta14_zeta7;

logic [(3*DATA_WIDTH)-1:0] zeta33_zeta32_zeta16;
logic [(3*DATA_WIDTH)-1:0] zeta35_zeta34_zeta17;
logic [(3*DATA_WIDTH)-1:0] zeta37_zeta36_zeta18;
logic [(3*DATA_WIDTH)-1:0] zeta39_zeta38_zeta19;
logic [(3*DATA_WIDTH)-1:0] zeta41_zeta40_zeta20;
logic [(3*DATA_WIDTH)-1:0] zeta43_zeta42_zeta21;
logic [(3*DATA_WIDTH)-1:0] zeta45_zeta44_zeta22;
logic [(3*DATA_WIDTH)-1:0] zeta47_zeta46_zeta23;
logic [(3*DATA_WIDTH)-1:0] zeta49_zeta48_zeta24;
logic [(3*DATA_WIDTH)-1:0] zeta51_zeta50_zeta25;
logic [(3*DATA_WIDTH)-1:0] zeta53_zeta52_zeta26;
logic [(3*DATA_WIDTH)-1:0] zeta55_zeta54_zeta27;
logic [(3*DATA_WIDTH)-1:0] zeta57_zeta56_zeta28;
logic [(3*DATA_WIDTH)-1:0] zeta59_zeta58_zeta29;
logic [(3*DATA_WIDTH)-1:0] zeta61_zeta60_zeta30;
logic [(3*DATA_WIDTH)-1:0] zeta63_zeta62_zeta31;

logic [(3*DATA_WIDTH-1):0] zeta129_zeta128_zeta64;
logic [(3*DATA_WIDTH-1):0] zeta131_zeta130_zeta65;
logic [(3*DATA_WIDTH-1):0] zeta133_zeta132_zeta66;
logic [(3*DATA_WIDTH-1):0] zeta135_zeta134_zeta67;
logic [(3*DATA_WIDTH-1):0] zeta137_zeta136_zeta68;
logic [(3*DATA_WIDTH-1):0] zeta139_zeta138_zeta69;
logic [(3*DATA_WIDTH-1):0] zeta141_zeta140_zeta70;
logic [(3*DATA_WIDTH-1):0] zeta143_zeta142_zeta71;
logic [(3*DATA_WIDTH-1):0] zeta145_zeta144_zeta72;
logic [(3*DATA_WIDTH-1):0] zeta147_zeta146_zeta73;
logic [(3*DATA_WIDTH-1):0] zeta149_zeta148_zeta74;
logic [(3*DATA_WIDTH-1):0] zeta151_zeta150_zeta75;
logic [(3*DATA_WIDTH-1):0] zeta153_zeta152_zeta76;
logic [(3*DATA_WIDTH-1):0] zeta155_zeta154_zeta77;
logic [(3*DATA_WIDTH-1):0] zeta157_zeta156_zeta78;
logic [(3*DATA_WIDTH-1):0] zeta159_zeta158_zeta79;
logic [(3*DATA_WIDTH-1):0] zeta161_zeta160_zeta80;
logic [(3*DATA_WIDTH-1):0] zeta163_zeta162_zeta81;
logic [(3*DATA_WIDTH-1):0] zeta165_zeta164_zeta82;
logic [(3*DATA_WIDTH-1):0] zeta167_zeta166_zeta83;
logic [(3*DATA_WIDTH-1):0] zeta169_zeta168_zeta84;
logic [(3*DATA_WIDTH-1):0] zeta171_zeta170_zeta85;
logic [(3*DATA_WIDTH-1):0] zeta173_zeta172_zeta86;
logic [(3*DATA_WIDTH-1):0] zeta175_zeta174_zeta87;
logic [(3*DATA_WIDTH-1):0] zeta177_zeta176_zeta88;
logic [(3*DATA_WIDTH-1):0] zeta179_zeta178_zeta89;
logic [(3*DATA_WIDTH-1):0] zeta181_zeta180_zeta90;
logic [(3*DATA_WIDTH-1):0] zeta183_zeta182_zeta91;
logic [(3*DATA_WIDTH-1):0] zeta185_zeta184_zeta92;
logic [(3*DATA_WIDTH-1):0] zeta187_zeta186_zeta93;
logic [(3*DATA_WIDTH-1):0] zeta189_zeta188_zeta94;
logic [(3*DATA_WIDTH-1):0] zeta191_zeta190_zeta95;
logic [(3*DATA_WIDTH-1):0] zeta193_zeta192_zeta96;
logic [(3*DATA_WIDTH-1):0] zeta195_zeta194_zeta97;
logic [(3*DATA_WIDTH-1):0] zeta197_zeta196_zeta98;
logic [(3*DATA_WIDTH-1):0] zeta199_zeta198_zeta99;
logic [(3*DATA_WIDTH-1):0] zeta201_zeta200_zeta100;
logic [(3*DATA_WIDTH-1):0] zeta203_zeta202_zeta101;
logic [(3*DATA_WIDTH-1):0] zeta205_zeta204_zeta102;
logic [(3*DATA_WIDTH-1):0] zeta207_zeta206_zeta103;
logic [(3*DATA_WIDTH-1):0] zeta209_zeta208_zeta104;
logic [(3*DATA_WIDTH-1):0] zeta211_zeta210_zeta105;
logic [(3*DATA_WIDTH-1):0] zeta213_zeta212_zeta106;
logic [(3*DATA_WIDTH-1):0] zeta215_zeta214_zeta107;
logic [(3*DATA_WIDTH-1):0] zeta217_zeta216_zeta108;
logic [(3*DATA_WIDTH-1):0] zeta219_zeta218_zeta109;
logic [(3*DATA_WIDTH-1):0] zeta221_zeta220_zeta110;
logic [(3*DATA_WIDTH-1):0] zeta223_zeta222_zeta111;
logic [(3*DATA_WIDTH-1):0] zeta225_zeta224_zeta112;
logic [(3*DATA_WIDTH-1):0] zeta227_zeta226_zeta113;
logic [(3*DATA_WIDTH-1):0] zeta229_zeta228_zeta114;
logic [(3*DATA_WIDTH-1):0] zeta231_zeta230_zeta115;
logic [(3*DATA_WIDTH-1):0] zeta233_zeta232_zeta116;
logic [(3*DATA_WIDTH-1):0] zeta235_zeta234_zeta117;
logic [(3*DATA_WIDTH-1):0] zeta237_zeta236_zeta118;
logic [(3*DATA_WIDTH-1):0] zeta239_zeta238_zeta119;
logic [(3*DATA_WIDTH-1):0] zeta241_zeta240_zeta120;
logic [(3*DATA_WIDTH-1):0] zeta243_zeta242_zeta121;
logic [(3*DATA_WIDTH-1):0] zeta245_zeta244_zeta122;
logic [(3*DATA_WIDTH-1):0] zeta247_zeta246_zeta123;
logic [(3*DATA_WIDTH-1):0] zeta249_zeta248_zeta124;
logic [(3*DATA_WIDTH-1):0] zeta251_zeta250_zeta125;
logic [(3*DATA_WIDTH-1):0] zeta253_zeta252_zeta126;
logic [(3*DATA_WIDTH-1):0] zeta255_zeta254_zeta127;


assign zeta3_zeta2_zeta1      = {23'h396569, 23'h397567, 23'h495E02}; //{3, 2, 1}


assign zeta9_zeta8_zeta4      = {23'h360DD5, 23'h76B1AE, 23'h4F062B}; //{9, 8, 4};
assign zeta11_zeta10_zeta5    = {23'h207FE4, 23'h28EDB0, 23'h53DF73}; //{11, 10, 5};
assign zeta13_zeta12_zeta6    = {23'h70894A, 23'h397283, 23'h4FE033};
assign zeta15_zeta14_zeta7    = {23'h6D3DC8, 23'h088192, 23'h4F066B};

assign zeta33_zeta32_zeta16   = {23'h30911E, 23'h36F72A, 23'h4C7294};
assign zeta35_zeta34_zeta17   = {23'h492673, 23'h29D13F, 23'h41E0B4};
assign zeta37_zeta36_zeta18   = {23'h2010A2, 23'h50685F, 23'h28A3D2};
assign zeta39_zeta38_zeta19   = {23'h11B2C3, 23'h3887F7, 23'h66528A};
assign zeta41_zeta40_zeta20   = {23'h0E2BED, 23'h0603A4, 23'h4A18A7};
assign zeta43_zeta42_zeta21   = {23'h4A5F35, 23'h10B72C, 23'h794034};
assign zeta45_zeta44_zeta22   = {23'h428CD4, 23'h1F9D15, 23'h0A52EE};
assign zeta47_zeta46_zeta23   = {23'h20E612, 23'h3177F4, 23'h6B7D81};
assign zeta49_zeta48_zeta24   = {23'h1AD873, 23'h341C1D, 23'h4E9F1D};
assign zeta51_zeta50_zeta25   = {23'h49553F, 23'h736681, 23'h1A2877};
assign zeta53_zeta52_zeta26   = {23'h62564A, 23'h3952F6, 23'h2571DF};
assign zeta55_zeta54_zeta27   = {23'h439A1C, 23'h65AD05, 23'h1649EE};
assign zeta57_zeta56_zeta28   = {23'h30B622, 23'h53AA5F, 23'h7611BD};
assign zeta59_zeta58_zeta29   = {23'h3B0E6D, 23'h087F38, 23'h492BB7};
assign zeta61_zeta60_zeta30   = {23'h1C496E, 23'h2C83DA, 23'h2AF697};
assign zeta63_zeta62_zeta31   = {23'h1C5B70, 23'h330E2B, 23'h22D8D5};

assign zeta129_zeta128_zeta64  = {23'h6257C5, 23'h0006D9, 23'h2EE3F1};
assign zeta131_zeta130_zeta65  = {23'h69A8EF, 23'h574B3C, 23'h137EB9};
assign zeta133_zeta132_zeta66  = {23'h64B5FE, 23'h289838, 23'h57A930};
assign zeta135_zeta134_zeta67  = {23'h2A4E78, 23'h7EF8F5, 23'h3AC6EF};
assign zeta137_zeta136_zeta68  = {23'h0154A8, 23'h120A23, 23'h3FD54C};
assign zeta139_zeta138_zeta69  = {23'h435E87, 23'h09B7FF, 23'h4EB2EA};
assign zeta141_zeta140_zeta70  = {23'h5CD5B4, 23'h437FF8, 23'h503EE1};
assign zeta143_zeta142_zeta71  = {23'h4728AF, 23'h4DC04E, 23'h7BB175};
assign zeta145_zeta144_zeta72  = {23'h0C8D0D, 23'h7F735D, 23'h2648B4};
assign zeta147_zeta146_zeta73  = {23'h5A6D80, 23'h0F66D5, 23'h1EF256};
assign zeta149_zeta148_zeta74  = {23'h185D96, 23'h61AB98, 23'h1D90A2};
assign zeta151_zeta150_zeta75  = {23'h468298, 23'h437F31, 23'h45A6D4};
assign zeta153_zeta152_zeta76  = {23'h4BD579, 23'h662960, 23'h2AE59B};
assign zeta155_zeta154_zeta77  = {23'h465D8D, 23'h28DE06, 23'h52589C};
assign zeta157_zeta156_zeta78  = {23'h09B434, 23'h49B0E3, 23'h6EF1F5};
assign zeta159_zeta158_zeta79  = {23'h5A68B0, 23'h7C0DB3, 23'h3F7288};
assign zeta161_zeta160_zeta80  = {23'h64D3D5, 23'h409BA9, 23'h175102};
assign zeta163_zeta162_zeta81  = {23'h658591, 23'h21762A, 23'h075D59};
assign zeta165_zeta164_zeta82  = {23'h48C39B, 23'h246E39, 23'h1187BA};
assign zeta167_zeta166_zeta83  = {23'h4F5859, 23'h7BC759, 23'h52ACA9};
assign zeta169_zeta168_zeta84  = {23'h230923, 23'h392DB2, 23'h773E9E};
assign zeta171_zeta170_zeta85  = {23'h454DF2, 23'h12EB67, 23'h0296D8};
assign zeta173_zeta172_zeta86  = {23'h285424, 23'h30C31C, 23'h2592EC};
assign zeta175_zeta174_zeta87  = {23'h7FAF80, 23'h13232E, 23'h4CFF12};
assign zeta177_zeta176_zeta88  = {23'h022A0B, 23'h2DBFCB, 23'h404CE8};
assign zeta179_zeta178_zeta89  = {23'h26587A, 23'h7E832C, 23'h4AA582};
assign zeta181_zeta180_zeta90  = {23'h095B76, 23'h6B3375, 23'h1E54E6};
assign zeta183_zeta182_zeta91  = {23'h5E061E, 23'h6BE1CC, 23'h4F16C1};
assign zeta185_zeta184_zeta92  = {23'h628C37, 23'h78E00D, 23'h1A7E79};
assign zeta187_zeta186_zeta93  = {23'h4AE53C, 23'h3DA604, 23'h03978F};
assign zeta189_zeta188_zeta94  = {23'h6330BB, 23'h1F1D68, 23'h4E4817};
assign zeta191_zeta190_zeta95  = {23'h5EA06C, 23'h7361B8, 23'h31B859};
assign zeta193_zeta192_zeta96  = {23'h201FC6, 23'h671AC7, 23'h5884CC};
assign zeta195_zeta194_zeta97  = {23'h60D772, 23'h5BA4FF, 23'h1B4827};
assign zeta197_zeta196_zeta98  = {23'h6DE024, 23'h08F201, 23'h5B63D0};
assign zeta199_zeta198_zeta99  = {23'h56038E, 23'h080E6D, 23'h5D787A};
assign zeta201_zeta200_zeta100 = {23'h1E6D3E, 23'h695688, 23'h35225E};
assign zeta203_zeta202_zeta101 = {23'h6A9DFA, 23'h2603BD, 23'h400C7E};
assign zeta205_zeta204_zeta102 = {23'h6DBFD4, 23'h07C017, 23'h6C09D1};
assign zeta207_zeta206_zeta103 = {23'h63E1E3, 23'h74D0BD, 23'h5BD532};
assign zeta209_zeta208_zeta104 = {23'h7AB60D, 23'h519573, 23'h6BC4D3};
assign zeta211_zeta210_zeta105 = {23'h2DECD4, 23'h2867BA, 23'h258ECB};
assign zeta213_zeta212_zeta106 = {23'h3F4CF5, 23'h58018C, 23'h2E534C};
assign zeta215_zeta214_zeta107 = {23'h427E23, 23'h0B7009, 23'h097A6C};
assign zeta217_zeta216_zeta108 = {23'h273333, 23'h3CBD37, 23'h3B8820};
assign zeta219_zeta218_zeta109 = {23'h1A4B5D, 23'h673957, 23'h6D285C};
assign zeta221_zeta220_zeta110 = {23'h1EF206, 23'h196926, 23'h2CA4F8};
assign zeta223_zeta222_zeta111 = {23'h4C76C8, 23'h11C14E, 23'h337CAA};
assign zeta225_zeta224_zeta112 = {23'h7FB19A, 23'h3CF42F, 23'h14B2A0};
assign zeta227_zeta226_zeta113 = {23'h2E1669, 23'h6AF66C, 23'h558536};
assign zeta229_zeta228_zeta114 = {23'h034760, 23'h3352D6, 23'h28F186};
assign zeta231_zeta230_zeta115 = {23'h741E78, 23'h085260, 23'h55795D};
assign zeta233_zeta232_zeta116 = {23'h6F0A11, 23'h2F6316, 23'h4AF670};
assign zeta235_zeta234_zeta117 = {23'h776D0B, 23'h07C0F1, 23'h234A86};
assign zeta237_zeta236_zeta118 = {23'h345824, 23'h0D1FF0, 23'h75E826};
assign zeta239_zeta238_zeta119 = {23'h68C559, 23'h0223D4, 23'h78DE66};
assign zeta241_zeta240_zeta120 = {23'h2FAA32, 23'h5E8885, 23'h05528C};
assign zeta243_zeta242_zeta121 = {23'h5E6942, 23'h23FC65, 23'h7ADF59};
assign zeta245_zeta244_zeta122 = {23'h65ADB3, 23'h51E0ED, 23'h0F6E17};
assign zeta247_zeta246_zeta123 = {23'h79E1FE, 23'h2CA5E6, 23'h5BF3DA};
assign zeta249_zeta248_zeta124 = {23'h35E1DD, 23'h7B4064, 23'h459B7E};
assign zeta251_zeta250_zeta125 = {23'h464ADE, 23'h433AAC, 23'h628B34};
assign zeta253_zeta252_zeta126 = {23'h73F1CE, 23'h1CFE14, 23'h5DBECB};
assign zeta255_zeta254_zeta127 = {23'h74B6D7, 23'h10170E, 23'h1A9E7B};

//------------------------------------------------------------------------------------

logic [(3*DATA_WIDTH)-1:0] zetainv1_zetainv2_zetainv3;

logic [(3*DATA_WIDTH)-1:0] zetainv7_zetainv14_zetainv15;
logic [(3*DATA_WIDTH)-1:0] zetainv6_zetainv12_zetainv13;
logic [(3*DATA_WIDTH)-1:0] zetainv5_zetainv10_zetainv11;
logic [(3*DATA_WIDTH)-1:0] zetainv4_zetainv8_zetainv9;

logic [(3*DATA_WIDTH)-1:0] zetainv16_zetainv32_zetainv33;
logic [(3*DATA_WIDTH)-1:0] zetainv17_zetainv34_zetainv35;
logic [(3*DATA_WIDTH)-1:0] zetainv18_zetainv36_zetainv37;
logic [(3*DATA_WIDTH)-1:0] zetainv19_zetainv38_zetainv39;
logic [(3*DATA_WIDTH)-1:0] zetainv20_zetainv40_zetainv41;
logic [(3*DATA_WIDTH)-1:0] zetainv21_zetainv42_zetainv43;
logic [(3*DATA_WIDTH)-1:0] zetainv22_zetainv44_zetainv45;
logic [(3*DATA_WIDTH)-1:0] zetainv23_zetainv46_zetainv47;
logic [(3*DATA_WIDTH)-1:0] zetainv24_zetainv48_zetainv49;
logic [(3*DATA_WIDTH)-1:0] zetainv25_zetainv50_zetainv51;
logic [(3*DATA_WIDTH)-1:0] zetainv26_zetainv52_zetainv53;
logic [(3*DATA_WIDTH)-1:0] zetainv27_zetainv54_zetainv55;
logic [(3*DATA_WIDTH)-1:0] zetainv28_zetainv56_zetainv57;
logic [(3*DATA_WIDTH)-1:0] zetainv29_zetainv58_zetainv59;
logic [(3*DATA_WIDTH)-1:0] zetainv30_zetainv60_zetainv61;
logic [(3*DATA_WIDTH)-1:0] zetainv31_zetainv62_zetainv63;

logic [(3*DATA_WIDTH-1):0] zetainv64_zetainv128_zetainv129;
logic [(3*DATA_WIDTH-1):0] zetainv65_zetainv130_zetainv131;
logic [(3*DATA_WIDTH-1):0] zetainv66_zetainv132_zetainv133;
logic [(3*DATA_WIDTH-1):0] zetainv67_zetainv134_zetainv135;
logic [(3*DATA_WIDTH-1):0] zetainv68_zetainv136_zetainv137;
logic [(3*DATA_WIDTH-1):0] zetainv69_zetainv138_zetainv139;
logic [(3*DATA_WIDTH-1):0] zetainv70_zetainv140_zetainv141;
logic [(3*DATA_WIDTH-1):0] zetainv71_zetainv142_zetainv143;
logic [(3*DATA_WIDTH-1):0] zetainv72_zetainv144_zetainv145;
logic [(3*DATA_WIDTH-1):0] zetainv73_zetainv146_zetainv147;
logic [(3*DATA_WIDTH-1):0] zetainv74_zetainv148_zetainv149;
logic [(3*DATA_WIDTH-1):0] zetainv75_zetainv150_zetainv151;
logic [(3*DATA_WIDTH-1):0] zetainv76_zetainv152_zetainv153;
logic [(3*DATA_WIDTH-1):0] zetainv77_zetainv154_zetainv155;
logic [(3*DATA_WIDTH-1):0] zetainv78_zetainv156_zetainv157;
logic [(3*DATA_WIDTH-1):0] zetainv79_zetainv158_zetainv159;
logic [(3*DATA_WIDTH-1):0] zetainv80_zetainv160_zetainv161;
logic [(3*DATA_WIDTH-1):0] zetainv81_zetainv162_zetainv163;
logic [(3*DATA_WIDTH-1):0] zetainv82_zetainv164_zetainv165;
logic [(3*DATA_WIDTH-1):0] zetainv83_zetainv166_zetainv167;
logic [(3*DATA_WIDTH-1):0] zetainv84_zetainv168_zetainv169;
logic [(3*DATA_WIDTH-1):0] zetainv85_zetainv170_zetainv171;
logic [(3*DATA_WIDTH-1):0] zetainv86_zetainv172_zetainv173;
logic [(3*DATA_WIDTH-1):0] zetainv87_zetainv174_zetainv175;
logic [(3*DATA_WIDTH-1):0] zetainv88_zetainv176_zetainv177;
logic [(3*DATA_WIDTH-1):0] zetainv89_zetainv178_zetainv179;
logic [(3*DATA_WIDTH-1):0] zetainv90_zetainv180_zetainv181;
logic [(3*DATA_WIDTH-1):0] zetainv91_zetainv182_zetainv183;
logic [(3*DATA_WIDTH-1):0] zetainv92_zetainv184_zetainv185;
logic [(3*DATA_WIDTH-1):0] zetainv93_zetainv186_zetainv187;
logic [(3*DATA_WIDTH-1):0] zetainv94_zetainv188_zetainv189;
logic [(3*DATA_WIDTH-1):0] zetainv95_zetainv190_zetainv191;
logic [(3*DATA_WIDTH-1):0] zetainv96_zetainv192_zetainv193;
logic [(3*DATA_WIDTH-1):0] zetainv97_zetainv194_zetainv195;
logic [(3*DATA_WIDTH-1):0] zetainv98_zetainv196_zetainv197;
logic [(3*DATA_WIDTH-1):0] zetainv99_zetainv198_zetainv199;
logic [(3*DATA_WIDTH-1):0] zetainv100_zetainv200_zetainv201;
logic [(3*DATA_WIDTH-1):0] zetainv101_zetainv202_zetainv203;
logic [(3*DATA_WIDTH-1):0] zetainv102_zetainv204_zetainv205;
logic [(3*DATA_WIDTH-1):0] zetainv103_zetainv206_zetainv207;
logic [(3*DATA_WIDTH-1):0] zetainv104_zetainv208_zetainv209;
logic [(3*DATA_WIDTH-1):0] zetainv105_zetainv210_zetainv211;
logic [(3*DATA_WIDTH-1):0] zetainv106_zetainv212_zetainv213;
logic [(3*DATA_WIDTH-1):0] zetainv107_zetainv214_zetainv215;
logic [(3*DATA_WIDTH-1):0] zetainv108_zetainv216_zetainv217;
logic [(3*DATA_WIDTH-1):0] zetainv109_zetainv218_zetainv219;
logic [(3*DATA_WIDTH-1):0] zetainv110_zetainv220_zetainv221;
logic [(3*DATA_WIDTH-1):0] zetainv111_zetainv222_zetainv223;
logic [(3*DATA_WIDTH-1):0] zetainv112_zetainv224_zetainv225;
logic [(3*DATA_WIDTH-1):0] zetainv113_zetainv226_zetainv227;
logic [(3*DATA_WIDTH-1):0] zetainv114_zetainv228_zetainv229;
logic [(3*DATA_WIDTH-1):0] zetainv115_zetainv230_zetainv231;
logic [(3*DATA_WIDTH-1):0] zetainv116_zetainv232_zetainv233;
logic [(3*DATA_WIDTH-1):0] zetainv117_zetainv234_zetainv235;
logic [(3*DATA_WIDTH-1):0] zetainv118_zetainv236_zetainv237;
logic [(3*DATA_WIDTH-1):0] zetainv119_zetainv238_zetainv239;
logic [(3*DATA_WIDTH-1):0] zetainv120_zetainv240_zetainv241;
logic [(3*DATA_WIDTH-1):0] zetainv121_zetainv242_zetainv243;
logic [(3*DATA_WIDTH-1):0] zetainv122_zetainv244_zetainv245;
logic [(3*DATA_WIDTH-1):0] zetainv123_zetainv246_zetainv247;
logic [(3*DATA_WIDTH-1):0] zetainv124_zetainv248_zetainv249;
logic [(3*DATA_WIDTH-1):0] zetainv125_zetainv250_zetainv251;
logic [(3*DATA_WIDTH-1):0] zetainv126_zetainv252_zetainv253;
logic [(3*DATA_WIDTH-1):0] zetainv127_zetainv254_zetainv255;


assign zetainv1_zetainv2_zetainv3      = {23'h3681FF, 23'h466A9A, 23'h467A98};

assign zetainv7_zetainv14_zetainv15    = {23'h30D996, 23'h775E6F, 23'h12A239}; //{7, 14, 15};
assign zetainv6_zetainv12_zetainv13    = {23'h2FFFCE, 23'h466D7E, 23'h0F56B7}; //{6, 12, 13};
assign zetainv5_zetainv10_zetainv11    = {23'h2C008E, 23'h56F251, 23'h5F601D}; //5, 10, 11;
assign zetainv4_zetainv8_zetainv9      = {23'h30D9D6, 23'h092E53, 23'h49D22C}; //4, 8 , 9;

assign zetainv16_zetainv32_zetainv33   = {23'h336D6D, 23'h48E8D7, 23'h4F4EE3};
assign zetainv17_zetainv34_zetainv35   = {23'h3DFF4D, 23'h560EC2, 23'h36B98E};
assign zetainv18_zetainv36_zetainv37   = {23'h573C2F, 23'h2F77A2, 23'h5FCF5F};
assign zetainv19_zetainv38_zetainv39   = {23'h198D77, 23'h47580A, 23'h6E2D3E};
assign zetainv20_zetainv40_zetainv41   = {23'h35C75A, 23'h79DC5D, 23'h71B414};
assign zetainv21_zetainv42_zetainv43   = {23'h069FCD, 23'h6F28D5, 23'h3580CC};
assign zetainv22_zetainv44_zetainv45   = {23'h758D13, 23'h6042EC, 23'h3D532D};
assign zetainv23_zetainv46_zetainv47   = {23'h146280, 23'h4E680D, 23'h5EF9EF};
assign zetainv24_zetainv48_zetainv49   = {23'h3140E4, 23'h4BC3E4, 23'h65078E};
assign zetainv25_zetainv50_zetainv51   = {23'h65B78A, 23'h0C7980, 23'h368AC2};
assign zetainv26_zetainv52_zetainv53   = {23'h5A6E22, 23'h468D0B, 23'h1D89B7};
assign zetainv27_zetainv54_zetainv55   = {23'h699613, 23'h1A32FC, 23'h3C45E5};
assign zetainv28_zetainv56_zetainv57   = {23'h09CE44, 23'h2C35A2, 23'h4F29DF};
assign zetainv29_zetainv58_zetainv59   = {23'h36B44A, 23'h7760C9, 23'h44D194};
assign zetainv30_zetainv60_zetainv61   = {23'h54E96A, 23'h535C27, 23'h639693};
assign zetainv31_zetainv62_zetainv63   = {23'h5D072C, 23'h4CD1D6, 23'h638491};

assign zetainv64_zetainv128_zetainv129  = {23'h50FC10, 23'h7FD928, 23'h1D883C};
assign zetainv65_zetainv130_zetainv131  = {23'h6C6148, 23'h2894C5, 23'h163712};
assign zetainv66_zetainv132_zetainv133  = {23'h2836D1, 23'h5747C9, 23'h1B2A03};
assign zetainv67_zetainv134_zetainv135  = {23'h451912, 23'h00E70C, 23'h559189};
assign zetainv68_zetainv136_zetainv137  = {23'h400AB5, 23'h6DD5DE, 23'h7E8B59};
assign zetainv69_zetainv138_zetainv139  = {23'h312D17, 23'h762802, 23'h3C817A};
assign zetainv70_zetainv140_zetainv141  = {23'h2FA120, 23'h3C6009, 23'h230A4D};
assign zetainv71_zetainv142_zetainv143  = {23'h042E8C, 23'h321FB3, 23'h38B752};
assign zetainv72_zetainv144_zetainv145  = {23'h59974D, 23'h006CA4, 23'h7352F4};
assign zetainv73_zetainv146_zetainv147  = {23'h60EDAB, 23'h70792C, 23'h257281};
assign zetainv74_zetainv148_zetainv149  = {23'h624F5F, 23'h1E3469, 23'h67826B};
assign zetainv75_zetainv150_zetainv151  = {23'h3A392D, 23'h3C60D0, 23'h395D69};
assign zetainv76_zetainv152_zetainv153  = {23'h54FA66, 23'h19B6A1, 23'h340A88};
assign zetainv77_zetainv154_zetainv155  = {23'h2D8765, 23'h5701FB, 23'h398274};
assign zetainv78_zetainv156_zetainv157  = {23'h10EE0C, 23'h362F1E, 23'h762BCD};
assign zetainv79_zetainv158_zetainv159  = {23'h406D79, 23'h03D24E, 23'h257751};
assign zetainv80_zetainv160_zetainv161  = {23'h688EFF, 23'h3F4458, 23'h1B0C2C};
assign zetainv81_zetainv162_zetainv163  = {23'h7882A8, 23'h5E69D7, 23'h1A5A70};
assign zetainv82_zetainv164_zetainv165  = {23'h6E5847, 23'h5B71C8, 23'h371C66};
assign zetainv83_zetainv166_zetainv167  = {23'h2D3358, 23'h0418A8, 23'h3087A8};
assign zetainv84_zetainv168_zetainv169  = {23'h08A163, 23'h46B24F, 23'h5CD6DE};
assign zetainv85_zetainv170_zetainv171  = {23'h7D4929, 23'h6CF49A, 23'h3A920F};
assign zetainv86_zetainv172_zetainv173  = {23'h5A4D15, 23'h4F1CE5, 23'h578BDD};
assign zetainv87_zetainv174_zetainv175  = {23'h32E0EF, 23'h6CBCD3, 23'h003081};
assign zetainv88_zetainv176_zetainv177  = {23'h3F9319, 23'h522036, 23'h7DB5F6};
assign zetainv89_zetainv178_zetainv179  = {23'h353A7F, 23'h015CD5, 23'h598787};
assign zetainv90_zetainv180_zetainv181  = {23'h618B1B, 23'h14AC8C, 23'h76848B};
assign zetainv91_zetainv182_zetainv183  = {23'h30C940, 23'h13FE35, 23'h21D9E3};
assign zetainv92_zetainv184_zetainv185  = {23'h656188, 23'h06FFF4, 23'h1D53CA};
assign zetainv93_zetainv186_zetainv187  = {23'h7C4872, 23'h4239FD, 23'h34FAC5};
assign zetainv94_zetainv188_zetainv189  = {23'h3197EA, 23'h60C299, 23'h1CAF46};
assign zetainv95_zetainv190_zetainv191  = {23'h4E27A8, 23'h0C7E49, 23'h213F95};
assign zetainv96_zetainv192_zetainv193  = {23'h275B35, 23'h18C53A, 23'h5FC03B};
assign zetainv97_zetainv194_zetainv195  = {23'h6497DA, 23'h243B02, 23'h1F088F};
assign zetainv98_zetainv196_zetainv197  = {23'h247C31, 23'h76EE00, 23'h11FFDD};
assign zetainv99_zetainv198_zetainv199  = {23'h226787, 23'h77D194, 23'h29DC73};
assign zetainv100_zetainv200_zetainv201 = {23'h4ABDA3, 23'h168979, 23'h6172C3};
assign zetainv101_zetainv202_zetainv203 = {23'h3FD383, 23'h59DC44, 23'h154207};
assign zetainv102_zetainv204_zetainv205 = {23'h13D630, 23'h781FEA, 23'h12202D};
assign zetainv103_zetainv206_zetainv207 = {23'h240ACF, 23'h0B0F44, 23'h1BFE1E};
assign zetainv104_zetainv208_zetainv209 = {23'h141B2E, 23'h2E4A8E, 23'h0529F4};
assign zetainv105_zetainv210_zetainv211 = {23'h5A5136, 23'h577847, 23'h51F32D};
assign zetainv106_zetainv212_zetainv213 = {23'h518CB5, 23'h27DE75, 23'h40930C};
assign zetainv107_zetainv214_zetainv215 = {23'h766595, 23'h746FF8, 23'h3D61DE};
assign zetainv108_zetainv216_zetainv217 = {23'h4457E1, 23'h4322CA, 23'h58ACCE};
assign zetainv109_zetainv218_zetainv219 = {23'h12B7A5, 23'h18A6AA, 23'h6594A4};
assign zetainv110_zetainv220_zetainv221 = {23'h533B09, 23'h6676DB, 23'h60EDFB};
assign zetainv111_zetainv222_zetainv223 = {23'h4C6357, 23'h6E1EB3, 23'h336939};
assign zetainv112_zetainv224_zetainv225 = {23'h6B2D61, 23'h42EBD2, 23'h002E67};
assign zetainv113_zetainv226_zetainv227 = {23'h2A5ACB, 23'h14E995, 23'h51C998};
assign zetainv114_zetainv228_zetainv229 = {23'h56EE7B, 23'h4C8D2B, 23'h7C98A1};
assign zetainv115_zetainv230_zetainv231 = {23'h2A66A4, 23'h778DA1, 23'h0BC189};
assign zetainv116_zetainv232_zetainv233 = {23'h34E991, 23'h507CEB, 23'h10D5F0};
assign zetainv117_zetainv234_zetainv235 = {23'h5C957B, 23'h781F10, 23'h0872F6};
assign zetainv118_zetainv236_zetainv237 = {23'h09F7DB, 23'h72C011, 23'h4B87DD};
assign zetainv119_zetainv238_zetainv239 = {23'h07019B, 23'h7DBC2D, 23'h171AA8};
assign zetainv120_zetainv240_zetainv241 = {23'h7A8D75, 23'h21577C, 23'h5035CF};
assign zetainv121_zetainv242_zetainv243 = {23'h0500A8, 23'h5BE39C, 23'h2176BF};
assign zetainv122_zetainv244_zetainv245 = {23'h7071EA, 23'h2DFF14, 23'h1A324E};
assign zetainv123_zetainv246_zetainv247 = {23'h23EC27, 23'h533A1B, 23'h05FE03};
assign zetainv124_zetainv248_zetainv249 = {23'h3A4483, 23'h049F9D, 23'h49FE24};
assign zetainv125_zetainv250_zetainv251 = {23'h1D54CD, 23'h3CA555, 23'h399523};
assign zetainv126_zetainv252_zetainv253 = {23'h222136, 23'h62E1ED, 23'h0BEE33};
assign zetainv127_zetainv254_zetainv255 = {23'h654186, 23'h6FC8F3, 23'h0B292A};

// assign ntt_twiddle_mem[0]  = 'h000001;
assign ntt_twiddle_mem[0 ] = zeta3_zeta2_zeta1  ;
assign ntt_twiddle_mem[1 ] = zeta9_zeta8_zeta4  ;
assign ntt_twiddle_mem[2 ] = zeta11_zeta10_zeta5;
assign ntt_twiddle_mem[3 ] = zeta13_zeta12_zeta6;
assign ntt_twiddle_mem[4 ] = zeta15_zeta14_zeta7;
assign ntt_twiddle_mem[5 ] = zeta33_zeta32_zeta16;
assign ntt_twiddle_mem[6 ] = zeta35_zeta34_zeta17;
assign ntt_twiddle_mem[7 ] = zeta37_zeta36_zeta18;
assign ntt_twiddle_mem[8 ] = zeta39_zeta38_zeta19;
assign ntt_twiddle_mem[9 ] = zeta41_zeta40_zeta20;
assign ntt_twiddle_mem[10] = zeta43_zeta42_zeta21;
assign ntt_twiddle_mem[11] = zeta45_zeta44_zeta22;
assign ntt_twiddle_mem[12] = zeta47_zeta46_zeta23;
assign ntt_twiddle_mem[13] = zeta49_zeta48_zeta24;
assign ntt_twiddle_mem[14] = zeta51_zeta50_zeta25;
assign ntt_twiddle_mem[15] = zeta53_zeta52_zeta26;
assign ntt_twiddle_mem[16] = zeta55_zeta54_zeta27;
assign ntt_twiddle_mem[17] = zeta57_zeta56_zeta28;
assign ntt_twiddle_mem[18] = zeta59_zeta58_zeta29;
assign ntt_twiddle_mem[19] = zeta61_zeta60_zeta30;
assign ntt_twiddle_mem[20] = zeta63_zeta62_zeta31;
assign ntt_twiddle_mem[21] = zeta129_zeta128_zeta64 ;
assign ntt_twiddle_mem[22] = zeta131_zeta130_zeta65 ;
assign ntt_twiddle_mem[23] = zeta133_zeta132_zeta66 ;
assign ntt_twiddle_mem[24] = zeta135_zeta134_zeta67 ;
assign ntt_twiddle_mem[25] = zeta137_zeta136_zeta68 ;
assign ntt_twiddle_mem[26] = zeta139_zeta138_zeta69 ;
assign ntt_twiddle_mem[27] = zeta141_zeta140_zeta70 ;
assign ntt_twiddle_mem[28] = zeta143_zeta142_zeta71 ;
assign ntt_twiddle_mem[29] = zeta145_zeta144_zeta72 ;
assign ntt_twiddle_mem[30] = zeta147_zeta146_zeta73 ;
assign ntt_twiddle_mem[31] = zeta149_zeta148_zeta74 ;
assign ntt_twiddle_mem[32] = zeta151_zeta150_zeta75 ;
assign ntt_twiddle_mem[33] = zeta153_zeta152_zeta76 ;
assign ntt_twiddle_mem[34] = zeta155_zeta154_zeta77 ;
assign ntt_twiddle_mem[35] = zeta157_zeta156_zeta78 ;
assign ntt_twiddle_mem[36] = zeta159_zeta158_zeta79 ;
assign ntt_twiddle_mem[37] = zeta161_zeta160_zeta80 ;
assign ntt_twiddle_mem[38] = zeta163_zeta162_zeta81 ;
assign ntt_twiddle_mem[39] = zeta165_zeta164_zeta82 ;
assign ntt_twiddle_mem[40] = zeta167_zeta166_zeta83 ;
assign ntt_twiddle_mem[41] = zeta169_zeta168_zeta84 ;
assign ntt_twiddle_mem[42] = zeta171_zeta170_zeta85 ;
assign ntt_twiddle_mem[43] = zeta173_zeta172_zeta86 ;
assign ntt_twiddle_mem[44] = zeta175_zeta174_zeta87 ;
assign ntt_twiddle_mem[45] = zeta177_zeta176_zeta88 ;
assign ntt_twiddle_mem[46] = zeta179_zeta178_zeta89 ;
assign ntt_twiddle_mem[47] = zeta181_zeta180_zeta90 ;
assign ntt_twiddle_mem[48] = zeta183_zeta182_zeta91 ;
assign ntt_twiddle_mem[49] = zeta185_zeta184_zeta92 ;
assign ntt_twiddle_mem[50] = zeta187_zeta186_zeta93 ;
assign ntt_twiddle_mem[51] = zeta189_zeta188_zeta94 ;
assign ntt_twiddle_mem[52] = zeta191_zeta190_zeta95 ;
assign ntt_twiddle_mem[53] = zeta193_zeta192_zeta96 ;
assign ntt_twiddle_mem[54] = zeta195_zeta194_zeta97 ;
assign ntt_twiddle_mem[55] = zeta197_zeta196_zeta98 ;
assign ntt_twiddle_mem[56] = zeta199_zeta198_zeta99 ;
assign ntt_twiddle_mem[57] = zeta201_zeta200_zeta100;
assign ntt_twiddle_mem[58] = zeta203_zeta202_zeta101;
assign ntt_twiddle_mem[59] = zeta205_zeta204_zeta102;
assign ntt_twiddle_mem[60] = zeta207_zeta206_zeta103;
assign ntt_twiddle_mem[61] = zeta209_zeta208_zeta104;
assign ntt_twiddle_mem[62] = zeta211_zeta210_zeta105;
assign ntt_twiddle_mem[63] = zeta213_zeta212_zeta106;
assign ntt_twiddle_mem[64] = zeta215_zeta214_zeta107;
assign ntt_twiddle_mem[65] = zeta217_zeta216_zeta108;
assign ntt_twiddle_mem[66] = zeta219_zeta218_zeta109;
assign ntt_twiddle_mem[67] = zeta221_zeta220_zeta110;
assign ntt_twiddle_mem[68] = zeta223_zeta222_zeta111;
assign ntt_twiddle_mem[69] = zeta225_zeta224_zeta112;
assign ntt_twiddle_mem[70] = zeta227_zeta226_zeta113;
assign ntt_twiddle_mem[71] = zeta229_zeta228_zeta114;
assign ntt_twiddle_mem[72] = zeta231_zeta230_zeta115;
assign ntt_twiddle_mem[73] = zeta233_zeta232_zeta116;
assign ntt_twiddle_mem[74] = zeta235_zeta234_zeta117;
assign ntt_twiddle_mem[75] = zeta237_zeta236_zeta118;
assign ntt_twiddle_mem[76] = zeta239_zeta238_zeta119;
assign ntt_twiddle_mem[77] = zeta241_zeta240_zeta120;
assign ntt_twiddle_mem[78] = zeta243_zeta242_zeta121;
assign ntt_twiddle_mem[79] = zeta245_zeta244_zeta122;
assign ntt_twiddle_mem[80] = zeta247_zeta246_zeta123;
assign ntt_twiddle_mem[81] = zeta249_zeta248_zeta124;
assign ntt_twiddle_mem[82] = zeta251_zeta250_zeta125;
assign ntt_twiddle_mem[83] = zeta253_zeta252_zeta126;
assign ntt_twiddle_mem[84] = zeta255_zeta254_zeta127;
//--------------------------------------------------------
// assign intt_twiddle_mem[0]  = 'h7FE000;
assign intt_twiddle_mem[0]  = zetainv127_zetainv254_zetainv255;
assign intt_twiddle_mem[1]  = zetainv126_zetainv252_zetainv253;
assign intt_twiddle_mem[2]  = zetainv125_zetainv250_zetainv251;
assign intt_twiddle_mem[3]  = zetainv124_zetainv248_zetainv249;
assign intt_twiddle_mem[4]  = zetainv123_zetainv246_zetainv247;
assign intt_twiddle_mem[5]  = zetainv122_zetainv244_zetainv245;
assign intt_twiddle_mem[6]  = zetainv121_zetainv242_zetainv243;
assign intt_twiddle_mem[7]  = zetainv120_zetainv240_zetainv241;
assign intt_twiddle_mem[8]  = zetainv119_zetainv238_zetainv239;
assign intt_twiddle_mem[9]  = zetainv118_zetainv236_zetainv237;
assign intt_twiddle_mem[10] = zetainv117_zetainv234_zetainv235;
assign intt_twiddle_mem[11] = zetainv116_zetainv232_zetainv233;
assign intt_twiddle_mem[12] = zetainv115_zetainv230_zetainv231;
assign intt_twiddle_mem[13] = zetainv114_zetainv228_zetainv229;
assign intt_twiddle_mem[14] = zetainv113_zetainv226_zetainv227;
assign intt_twiddle_mem[15] = zetainv112_zetainv224_zetainv225;
assign intt_twiddle_mem[16] = zetainv111_zetainv222_zetainv223;
assign intt_twiddle_mem[17] = zetainv110_zetainv220_zetainv221;
assign intt_twiddle_mem[18] = zetainv109_zetainv218_zetainv219;
assign intt_twiddle_mem[19] = zetainv108_zetainv216_zetainv217;
assign intt_twiddle_mem[20] = zetainv107_zetainv214_zetainv215;
assign intt_twiddle_mem[21] = zetainv106_zetainv212_zetainv213;
assign intt_twiddle_mem[22] = zetainv105_zetainv210_zetainv211;
assign intt_twiddle_mem[23] = zetainv104_zetainv208_zetainv209;
assign intt_twiddle_mem[24] = zetainv103_zetainv206_zetainv207;
assign intt_twiddle_mem[25] = zetainv102_zetainv204_zetainv205;
assign intt_twiddle_mem[26] = zetainv101_zetainv202_zetainv203;
assign intt_twiddle_mem[27] = zetainv100_zetainv200_zetainv201;
assign intt_twiddle_mem[28] = zetainv99_zetainv198_zetainv199 ;
assign intt_twiddle_mem[29] = zetainv98_zetainv196_zetainv197 ;
assign intt_twiddle_mem[30] = zetainv97_zetainv194_zetainv195 ;
assign intt_twiddle_mem[31] = zetainv96_zetainv192_zetainv193 ;
assign intt_twiddle_mem[32] = zetainv95_zetainv190_zetainv191 ;
assign intt_twiddle_mem[33] = zetainv94_zetainv188_zetainv189 ;
assign intt_twiddle_mem[34] = zetainv93_zetainv186_zetainv187 ;
assign intt_twiddle_mem[35] = zetainv92_zetainv184_zetainv185 ;
assign intt_twiddle_mem[36] = zetainv91_zetainv182_zetainv183 ;
assign intt_twiddle_mem[37] = zetainv90_zetainv180_zetainv181 ;
assign intt_twiddle_mem[38] = zetainv89_zetainv178_zetainv179 ;
assign intt_twiddle_mem[39] = zetainv88_zetainv176_zetainv177 ;
assign intt_twiddle_mem[40] = zetainv87_zetainv174_zetainv175 ;
assign intt_twiddle_mem[41] = zetainv86_zetainv172_zetainv173 ;
assign intt_twiddle_mem[42] = zetainv85_zetainv170_zetainv171 ;
assign intt_twiddle_mem[43] = zetainv84_zetainv168_zetainv169 ;
assign intt_twiddle_mem[44] = zetainv83_zetainv166_zetainv167 ;
assign intt_twiddle_mem[45] = zetainv82_zetainv164_zetainv165 ;
assign intt_twiddle_mem[46] = zetainv81_zetainv162_zetainv163 ;
assign intt_twiddle_mem[47] = zetainv80_zetainv160_zetainv161 ;
assign intt_twiddle_mem[48] = zetainv79_zetainv158_zetainv159 ;
assign intt_twiddle_mem[49] = zetainv78_zetainv156_zetainv157 ;
assign intt_twiddle_mem[50] = zetainv77_zetainv154_zetainv155 ;
assign intt_twiddle_mem[51] = zetainv76_zetainv152_zetainv153 ;
assign intt_twiddle_mem[52] = zetainv75_zetainv150_zetainv151 ;
assign intt_twiddle_mem[53] = zetainv74_zetainv148_zetainv149 ;
assign intt_twiddle_mem[54] = zetainv73_zetainv146_zetainv147 ;
assign intt_twiddle_mem[55] = zetainv72_zetainv144_zetainv145 ;
assign intt_twiddle_mem[56] = zetainv71_zetainv142_zetainv143 ;
assign intt_twiddle_mem[57] = zetainv70_zetainv140_zetainv141 ;
assign intt_twiddle_mem[58] = zetainv69_zetainv138_zetainv139 ;
assign intt_twiddle_mem[59] = zetainv68_zetainv136_zetainv137 ;
assign intt_twiddle_mem[60] = zetainv67_zetainv134_zetainv135 ;
assign intt_twiddle_mem[61] = zetainv66_zetainv132_zetainv133 ;
assign intt_twiddle_mem[62] = zetainv65_zetainv130_zetainv131 ;
assign intt_twiddle_mem[63] = zetainv64_zetainv128_zetainv129 ;
assign intt_twiddle_mem[64] = zetainv31_zetainv62_zetainv63;
assign intt_twiddle_mem[65] = zetainv30_zetainv60_zetainv61;
assign intt_twiddle_mem[66] = zetainv29_zetainv58_zetainv59; 
assign intt_twiddle_mem[67] = zetainv28_zetainv56_zetainv57;
assign intt_twiddle_mem[68] = zetainv27_zetainv54_zetainv55;
assign intt_twiddle_mem[69] = zetainv26_zetainv52_zetainv53;
assign intt_twiddle_mem[70] = zetainv25_zetainv50_zetainv51;
assign intt_twiddle_mem[71] = zetainv24_zetainv48_zetainv49;
assign intt_twiddle_mem[72] = zetainv23_zetainv46_zetainv47;
assign intt_twiddle_mem[73] = zetainv22_zetainv44_zetainv45;
assign intt_twiddle_mem[74] = zetainv21_zetainv42_zetainv43;
assign intt_twiddle_mem[75] = zetainv20_zetainv40_zetainv41;
assign intt_twiddle_mem[76] = zetainv19_zetainv38_zetainv39;
assign intt_twiddle_mem[77] = zetainv18_zetainv36_zetainv37;
assign intt_twiddle_mem[78] = zetainv17_zetainv34_zetainv35;
assign intt_twiddle_mem[79] = zetainv16_zetainv32_zetainv33;
assign intt_twiddle_mem[80] = zetainv7_zetainv14_zetainv15;
assign intt_twiddle_mem[81] = zetainv6_zetainv12_zetainv13;
assign intt_twiddle_mem[82] = zetainv5_zetainv10_zetainv11;
assign intt_twiddle_mem[83] = zetainv4_zetainv8_zetainv9;
assign intt_twiddle_mem[84] = zetainv1_zetainv2_zetainv3;


endmodule