-- -h localhost -U postgres -d elixir-questionnaire
-- vim: syntax=pgsql:

drop table "Respondents" cascade;
create table "Respondents" (
	id serial primary key,
	name varchar(200) not null,
	key varchar(50) not null unique,
	accessed timestamp with time zone,
	finished timestamp with time zone
);
alter table "Respondents" owner to elixir;

-- create extension pgcrypto;
-- CREATE OR REPLACE FUNCTION sha1(bytea) returns text AS $$
--     SELECT encode(digest($1, 'sha1'), 'hex')
-- $$ LANGUAGE SQL STRICT IMMUTABLE;

insert into "Respondents" (name, key) values ('Testing Institute', 'test1');
insert into "Respondents" (name, key) values ('Institute of Molecular Genetics - Dept. of Genomics and Bioinformatics', 'imgdgb');
insert into "Respondents" (name, key) values ('Institute of Animal Physiology and Genetics - Laboratory of Fish Genetics ', 'iapglfg');

--------------------------------------------------------------------------

drop table "Results";
create table "Results" (
	id serial primary key,
	respondent_id int not null references "Respondents"(id),
	name varchar(50) not null,
	text varchar(200),
	value varchar(1000),
	constraint uniq_result unique (respondent_id, name)
);
alter table "Results" owner to elixir;
--insert into "Results" (respondent_id, name, text, value) values (1, 'x_y', 'item', 'val');